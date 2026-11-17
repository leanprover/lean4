// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.EPR.Pass
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic public import Lean.Meta.Tactic.BVDecide.EPR.BitVec import Lean.Meta.Sym.InstantiateMVarsS import Lean.Meta.Sym.InferType import Lean.Meta.Sym.SynthInstance import Lean.Meta.Tactic.BVDecide.EPR.SortInference
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
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_EprProblem_inferSorts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__2;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__1;
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerPred(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableProd___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__0_value)} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(159, 35, 146, 118, 24, 65, 174, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(90, 191, 239, 225, 113, 224, 109, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__15_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__17_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__18_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__20_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__8_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0_spec__1(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "epr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(98, 19, 168, 128, 92, 3, 227, 120)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Discarding fact as it mentions empty sorts: "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__0_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__1 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__1_value;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__2 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__2_value;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ofNonempty"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__3 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__3_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__4_value_aux_0),((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(197, 41, 144, 91, 215, 43, 73, 12)}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__4 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Detected EPR problem"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__1_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__2;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__3;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "predicate "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " over "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ground fact: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__5(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "quantified fact "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__6(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sort "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " with elements "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__18___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__19(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18_spec__20(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18_spec__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__20(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__20___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Learned hypothesis: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "eprDetectPass"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(222, 60, 173, 104, 3, 245, 95, 19)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__4(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_9_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__3));
v___x_10_ = lean_box(0);
v___x_11_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__2);
v___x_12_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_9_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__4, &l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__4);
return v___x_13_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default;
return v___x_14_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_box(0);
v___x_16_ = lean_unsigned_to_nat(16u);
v___x_17_ = lean_mk_array(v___x_16_, v___x_15_);
return v___x_17_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__0);
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
return v___x_20_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_23_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__2));
v___x_24_ = lean_unsigned_to_nat(0u);
v___x_25_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__1);
v___x_26_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
lean_ctor_set(v___x_26_, 2, v___x_24_);
lean_ctor_set(v___x_26_, 3, v___x_25_);
lean_ctor_set(v___x_26_, 4, v___x_25_);
lean_ctor_set(v___x_26_, 5, v___x_23_);
lean_ctor_set(v___x_26_, 6, v___x_23_);
lean_ctor_set(v___x_26_, 7, v___x_23_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg(lean_object* v_x_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3);
v___x_36_ = lean_st_mk_ref(v___x_35_);
lean_inc(v_a_33_);
lean_inc_ref(v_a_32_);
lean_inc(v_a_31_);
lean_inc_ref(v_a_30_);
lean_inc(v_a_29_);
lean_inc_ref(v_a_28_);
lean_inc(v___x_36_);
v___x_37_ = lean_apply_8(v_x_27_, v___x_36_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, lean_box(0));
if (lean_obj_tag(v___x_37_) == 0)
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_46_; 
v_a_38_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_46_ == 0)
{
v___x_40_ = v___x_37_;
v_isShared_41_ = v_isSharedCheck_46_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_37_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_46_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_42_ = lean_st_ref_get(v___x_36_);
lean_dec(v___x_36_);
lean_dec(v___x_42_);
if (v_isShared_41_ == 0)
{
v___x_44_ = v___x_40_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_38_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
else
{
lean_dec(v___x_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___boxed(lean_object* v_x_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg(v_x_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run(lean_object* v_00_u03b1_56_, lean_object* v_x_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3);
v___x_66_ = lean_st_mk_ref(v___x_65_);
lean_inc(v_a_63_);
lean_inc_ref(v_a_62_);
lean_inc(v_a_61_);
lean_inc_ref(v_a_60_);
lean_inc(v_a_59_);
lean_inc_ref(v_a_58_);
lean_inc(v___x_66_);
v___x_67_ = lean_apply_8(v_x_57_, v___x_66_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, lean_box(0));
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_76_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_76_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_76_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_72_ = lean_st_ref_get(v___x_66_);
lean_dec(v___x_66_);
lean_dec(v___x_72_);
if (v_isShared_71_ == 0)
{
v___x_74_ = v___x_70_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_68_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
else
{
lean_dec(v___x_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___boxed(lean_object* v_00_u03b1_77_, lean_object* v_x_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run(v_00_u03b1_77_, v_x_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg(lean_object* v_type_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___f_92_; lean_object* v___f_93_; lean_object* v___x_94_; lean_object* v_sortIds_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___f_92_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___closed__0));
v___f_93_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___closed__1));
v___x_94_ = lean_st_ref_get(v_a_90_);
v_sortIds_95_ = lean_ctor_get(v___x_94_, 1);
lean_inc_ref(v_sortIds_95_);
lean_dec(v___x_94_);
v___x_96_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_92_, v___f_93_, v_sortIds_95_, v_type_89_);
lean_dec_ref(v_sortIds_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___boxed(lean_object* v_type_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg(v_type_98_, v_a_99_);
lean_dec(v_a_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f(lean_object* v_type_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___x_113_; lean_object* v_sortIds_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___f_111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___closed__0));
v___f_112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___closed__1));
v___x_113_ = lean_st_ref_get(v_a_103_);
v_sortIds_114_ = lean_ctor_get(v___x_113_, 1);
lean_inc_ref(v_sortIds_114_);
lean_dec(v___x_113_);
v___x_115_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_111_, v___f_112_, v_sortIds_114_, v_type_102_);
lean_dec_ref(v_sortIds_114_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___boxed(lean_object* v_type_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f(v_type_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__2___redArg(lean_object* v_a_127_, lean_object* v_b_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
lean_dec(v_b_128_);
lean_dec(v_a_127_);
return v_x_129_;
}
else
{
lean_object* v_key_130_; lean_object* v_value_131_; lean_object* v_tail_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_144_; 
v_key_130_ = lean_ctor_get(v_x_129_, 0);
v_value_131_ = lean_ctor_get(v_x_129_, 1);
v_tail_132_ = lean_ctor_get(v_x_129_, 2);
v_isSharedCheck_144_ = !lean_is_exclusive(v_x_129_);
if (v_isSharedCheck_144_ == 0)
{
v___x_134_ = v_x_129_;
v_isShared_135_ = v_isSharedCheck_144_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_tail_132_);
lean_inc(v_value_131_);
lean_inc(v_key_130_);
lean_dec(v_x_129_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_144_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
uint8_t v___x_136_; 
v___x_136_ = lean_nat_dec_eq(v_key_130_, v_a_127_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__2___redArg(v_a_127_, v_b_128_, v_tail_132_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 2, v___x_137_);
v___x_139_ = v___x_134_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_key_130_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_value_131_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
else
{
lean_object* v___x_142_; 
lean_dec(v_value_131_);
lean_dec(v_key_130_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v_b_128_);
lean_ctor_set(v___x_134_, 0, v_a_127_);
v___x_142_ = v___x_134_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_127_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_b_128_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_tail_132_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___redArg(lean_object* v_a_145_, lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
uint8_t v___x_147_; 
v___x_147_ = 0;
return v___x_147_;
}
else
{
lean_object* v_key_148_; lean_object* v_tail_149_; uint8_t v___x_150_; 
v_key_148_ = lean_ctor_get(v_x_146_, 0);
v_tail_149_ = lean_ctor_get(v_x_146_, 2);
v___x_150_ = lean_nat_dec_eq(v_key_148_, v_a_145_);
if (v___x_150_ == 0)
{
v_x_146_ = v_tail_149_;
goto _start;
}
else
{
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___redArg___boxed(lean_object* v_a_152_, lean_object* v_x_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___redArg(v_a_152_, v_x_153_);
lean_dec(v_x_153_);
lean_dec(v_a_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
return v_x_156_;
}
else
{
lean_object* v_key_158_; lean_object* v_value_159_; lean_object* v_tail_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_183_; 
v_key_158_ = lean_ctor_get(v_x_157_, 0);
v_value_159_ = lean_ctor_get(v_x_157_, 1);
v_tail_160_ = lean_ctor_get(v_x_157_, 2);
v_isSharedCheck_183_ = !lean_is_exclusive(v_x_157_);
if (v_isSharedCheck_183_ == 0)
{
v___x_162_ = v_x_157_;
v_isShared_163_ = v_isSharedCheck_183_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_tail_160_);
lean_inc(v_value_159_);
lean_inc(v_key_158_);
lean_dec(v_x_157_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_183_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; uint64_t v___x_167_; uint64_t v_fold_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_164_ = lean_array_get_size(v_x_156_);
v___x_165_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_key_158_);
v___x_166_ = 32ULL;
v___x_167_ = lean_uint64_shift_right(v___x_165_, v___x_166_);
v_fold_168_ = lean_uint64_xor(v___x_165_, v___x_167_);
v___x_169_ = 16ULL;
v___x_170_ = lean_uint64_shift_right(v_fold_168_, v___x_169_);
v___x_171_ = lean_uint64_xor(v_fold_168_, v___x_170_);
v___x_172_ = lean_uint64_to_usize(v___x_171_);
v___x_173_ = lean_usize_of_nat(v___x_164_);
v___x_174_ = ((size_t)1ULL);
v___x_175_ = lean_usize_sub(v___x_173_, v___x_174_);
v___x_176_ = lean_usize_land(v___x_172_, v___x_175_);
v___x_177_ = lean_array_uget_borrowed(v_x_156_, v___x_176_);
lean_inc(v___x_177_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 2, v___x_177_);
v___x_179_ = v___x_162_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_key_158_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_value_159_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v___x_177_);
v___x_179_ = v_reuseFailAlloc_182_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; 
v___x_180_ = lean_array_uset(v_x_156_, v___x_176_, v___x_179_);
v_x_156_ = v___x_180_;
v_x_157_ = v_tail_160_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2___redArg(lean_object* v_i_184_, lean_object* v_source_185_, lean_object* v_target_186_){
_start:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = lean_array_get_size(v_source_185_);
v___x_188_ = lean_nat_dec_lt(v_i_184_, v___x_187_);
if (v___x_188_ == 0)
{
lean_dec_ref(v_source_185_);
lean_dec(v_i_184_);
return v_target_186_;
}
else
{
lean_object* v_es_189_; lean_object* v___x_190_; lean_object* v_source_191_; lean_object* v_target_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_es_189_ = lean_array_fget(v_source_185_, v_i_184_);
v___x_190_ = lean_box(0);
v_source_191_ = lean_array_fset(v_source_185_, v_i_184_, v___x_190_);
v_target_192_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2_spec__4___redArg(v_target_186_, v_es_189_);
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_add(v_i_184_, v___x_193_);
lean_dec(v_i_184_);
v_i_184_ = v___x_194_;
v_source_185_ = v_source_191_;
v_target_186_ = v_target_192_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1___redArg(lean_object* v_data_196_){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_nbuckets_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_197_ = lean_array_get_size(v_data_196_);
v___x_198_ = lean_unsigned_to_nat(2u);
v_nbuckets_199_ = lean_nat_mul(v___x_197_, v___x_198_);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_box(0);
v___x_202_ = lean_mk_array(v_nbuckets_199_, v___x_201_);
v___x_203_ = lean_array_propagate_mark(v_data_196_, v___x_202_);
v___x_204_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2___redArg(v___x_200_, v_data_196_, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0___redArg(lean_object* v_m_205_, lean_object* v_a_206_, lean_object* v_b_207_){
_start:
{
lean_object* v_size_208_; lean_object* v_buckets_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_252_; 
v_size_208_ = lean_ctor_get(v_m_205_, 0);
v_buckets_209_ = lean_ctor_get(v_m_205_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v_m_205_);
if (v_isSharedCheck_252_ == 0)
{
v___x_211_ = v_m_205_;
v_isShared_212_ = v_isSharedCheck_252_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_buckets_209_);
lean_inc(v_size_208_);
lean_dec(v_m_205_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_252_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; uint64_t v___x_214_; uint64_t v___x_215_; uint64_t v___x_216_; uint64_t v_fold_217_; uint64_t v___x_218_; uint64_t v___x_219_; uint64_t v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; size_t v___x_225_; lean_object* v_bkt_226_; uint8_t v___x_227_; 
v___x_213_ = lean_array_get_size(v_buckets_209_);
v___x_214_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_a_206_);
v___x_215_ = 32ULL;
v___x_216_ = lean_uint64_shift_right(v___x_214_, v___x_215_);
v_fold_217_ = lean_uint64_xor(v___x_214_, v___x_216_);
v___x_218_ = 16ULL;
v___x_219_ = lean_uint64_shift_right(v_fold_217_, v___x_218_);
v___x_220_ = lean_uint64_xor(v_fold_217_, v___x_219_);
v___x_221_ = lean_uint64_to_usize(v___x_220_);
v___x_222_ = lean_usize_of_nat(v___x_213_);
v___x_223_ = ((size_t)1ULL);
v___x_224_ = lean_usize_sub(v___x_222_, v___x_223_);
v___x_225_ = lean_usize_land(v___x_221_, v___x_224_);
v_bkt_226_ = lean_array_uget_borrowed(v_buckets_209_, v___x_225_);
v___x_227_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___redArg(v_a_206_, v_bkt_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v_size_x27_229_; lean_object* v___x_230_; lean_object* v_buckets_x27_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_228_ = lean_unsigned_to_nat(1u);
v_size_x27_229_ = lean_nat_add(v_size_208_, v___x_228_);
lean_dec(v_size_208_);
lean_inc(v_bkt_226_);
v___x_230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_230_, 0, v_a_206_);
lean_ctor_set(v___x_230_, 1, v_b_207_);
lean_ctor_set(v___x_230_, 2, v_bkt_226_);
v_buckets_x27_231_ = lean_array_uset(v_buckets_209_, v___x_225_, v___x_230_);
v___x_232_ = lean_unsigned_to_nat(4u);
v___x_233_ = lean_nat_mul(v_size_x27_229_, v___x_232_);
v___x_234_ = lean_unsigned_to_nat(3u);
v___x_235_ = lean_nat_div(v___x_233_, v___x_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_array_get_size(v_buckets_x27_231_);
v___x_237_ = lean_nat_dec_le(v___x_235_, v___x_236_);
lean_dec(v___x_235_);
if (v___x_237_ == 0)
{
lean_object* v_val_238_; lean_object* v___x_240_; 
v_val_238_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1___redArg(v_buckets_x27_231_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 1, v_val_238_);
lean_ctor_set(v___x_211_, 0, v_size_x27_229_);
v___x_240_ = v___x_211_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_size_x27_229_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_val_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
else
{
lean_object* v___x_243_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 1, v_buckets_x27_231_);
lean_ctor_set(v___x_211_, 0, v_size_x27_229_);
v___x_243_ = v___x_211_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_size_x27_229_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_buckets_x27_231_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
else
{
lean_object* v___x_245_; lean_object* v_buckets_x27_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
lean_inc(v_bkt_226_);
v___x_245_ = lean_box(0);
v_buckets_x27_246_ = lean_array_uset(v_buckets_209_, v___x_225_, v___x_245_);
v___x_247_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__2___redArg(v_a_206_, v_b_207_, v_bkt_226_);
v___x_248_ = lean_array_uset(v_buckets_x27_246_, v___x_225_, v___x_247_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 1, v___x_248_);
v___x_250_ = v___x_211_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_size_208_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__6___redArg(lean_object* v_a_253_, lean_object* v_b_254_, lean_object* v_x_255_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
lean_dec(v_b_254_);
lean_dec_ref(v_a_253_);
return v_x_255_;
}
else
{
lean_object* v_key_256_; lean_object* v_value_257_; lean_object* v_tail_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_272_; 
v_key_256_ = lean_ctor_get(v_x_255_, 0);
v_value_257_ = lean_ctor_get(v_x_255_, 1);
v_tail_258_ = lean_ctor_get(v_x_255_, 2);
v_isSharedCheck_272_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_272_ == 0)
{
v___x_260_ = v_x_255_;
v_isShared_261_ = v_isSharedCheck_272_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_tail_258_);
lean_inc(v_value_257_);
lean_inc(v_key_256_);
lean_dec(v_x_255_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_272_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
size_t v___x_262_; size_t v___x_263_; uint8_t v___x_264_; 
v___x_262_ = lean_ptr_addr(v_key_256_);
v___x_263_ = lean_ptr_addr(v_a_253_);
v___x_264_ = lean_usize_dec_eq(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__6___redArg(v_a_253_, v_b_254_, v_tail_258_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 2, v___x_265_);
v___x_267_ = v___x_260_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_key_256_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_value_257_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
else
{
lean_object* v___x_270_; 
lean_dec(v_value_257_);
lean_dec(v_key_256_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v_b_254_);
lean_ctor_set(v___x_260_, 0, v_a_253_);
v___x_270_ = v___x_260_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_253_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_b_254_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_tail_258_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7_spec__9___redArg(lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
return v_x_273_;
}
else
{
lean_object* v_key_275_; lean_object* v_value_276_; lean_object* v_tail_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_303_; 
v_key_275_ = lean_ctor_get(v_x_274_, 0);
v_value_276_ = lean_ctor_get(v_x_274_, 1);
v_tail_277_ = lean_ctor_get(v_x_274_, 2);
v_isSharedCheck_303_ = !lean_is_exclusive(v_x_274_);
if (v_isSharedCheck_303_ == 0)
{
v___x_279_ = v_x_274_;
v_isShared_280_ = v_isSharedCheck_303_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_tail_277_);
lean_inc(v_value_276_);
lean_inc(v_key_275_);
lean_dec(v_x_274_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_303_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; uint64_t v___x_285_; uint64_t v___x_286_; uint64_t v___x_287_; uint64_t v_fold_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; size_t v___x_295_; size_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_281_ = lean_array_get_size(v_x_273_);
v___x_282_ = lean_ptr_addr(v_key_275_);
v___x_283_ = ((size_t)3ULL);
v___x_284_ = lean_usize_shift_right(v___x_282_, v___x_283_);
v___x_285_ = lean_usize_to_uint64(v___x_284_);
v___x_286_ = 32ULL;
v___x_287_ = lean_uint64_shift_right(v___x_285_, v___x_286_);
v_fold_288_ = lean_uint64_xor(v___x_285_, v___x_287_);
v___x_289_ = 16ULL;
v___x_290_ = lean_uint64_shift_right(v_fold_288_, v___x_289_);
v___x_291_ = lean_uint64_xor(v_fold_288_, v___x_290_);
v___x_292_ = lean_uint64_to_usize(v___x_291_);
v___x_293_ = lean_usize_of_nat(v___x_281_);
v___x_294_ = ((size_t)1ULL);
v___x_295_ = lean_usize_sub(v___x_293_, v___x_294_);
v___x_296_ = lean_usize_land(v___x_292_, v___x_295_);
v___x_297_ = lean_array_uget_borrowed(v_x_273_, v___x_296_);
lean_inc(v___x_297_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 2, v___x_297_);
v___x_299_ = v___x_279_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_key_275_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_value_276_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v___x_297_);
v___x_299_ = v_reuseFailAlloc_302_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; 
v___x_300_ = lean_array_uset(v_x_273_, v___x_296_, v___x_299_);
v_x_273_ = v___x_300_;
v_x_274_ = v_tail_277_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7___redArg(lean_object* v_i_304_, lean_object* v_source_305_, lean_object* v_target_306_){
_start:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_array_get_size(v_source_305_);
v___x_308_ = lean_nat_dec_lt(v_i_304_, v___x_307_);
if (v___x_308_ == 0)
{
lean_dec_ref(v_source_305_);
lean_dec(v_i_304_);
return v_target_306_;
}
else
{
lean_object* v_es_309_; lean_object* v___x_310_; lean_object* v_source_311_; lean_object* v_target_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_es_309_ = lean_array_fget(v_source_305_, v_i_304_);
v___x_310_ = lean_box(0);
v_source_311_ = lean_array_fset(v_source_305_, v_i_304_, v___x_310_);
v_target_312_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7_spec__9___redArg(v_target_306_, v_es_309_);
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = lean_nat_add(v_i_304_, v___x_313_);
lean_dec(v_i_304_);
v_i_304_ = v___x_314_;
v_source_305_ = v_source_311_;
v_target_306_ = v_target_312_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5___redArg(lean_object* v_data_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_nbuckets_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_317_ = lean_array_get_size(v_data_316_);
v___x_318_ = lean_unsigned_to_nat(2u);
v_nbuckets_319_ = lean_nat_mul(v___x_317_, v___x_318_);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_box(0);
v___x_322_ = lean_mk_array(v_nbuckets_319_, v___x_321_);
v___x_323_ = lean_array_propagate_mark(v_data_316_, v___x_322_);
v___x_324_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7___redArg(v___x_320_, v_data_316_, v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4___redArg(lean_object* v_a_325_, lean_object* v_x_326_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
uint8_t v___x_327_; 
v___x_327_ = 0;
return v___x_327_;
}
else
{
lean_object* v_key_328_; lean_object* v_tail_329_; size_t v___x_330_; size_t v___x_331_; uint8_t v___x_332_; 
v_key_328_ = lean_ctor_get(v_x_326_, 0);
v_tail_329_ = lean_ctor_get(v_x_326_, 2);
v___x_330_ = lean_ptr_addr(v_key_328_);
v___x_331_ = lean_ptr_addr(v_a_325_);
v___x_332_ = lean_usize_dec_eq(v___x_330_, v___x_331_);
if (v___x_332_ == 0)
{
v_x_326_ = v_tail_329_;
goto _start;
}
else
{
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4___redArg___boxed(lean_object* v_a_334_, lean_object* v_x_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4___redArg(v_a_334_, v_x_335_);
lean_dec(v_x_335_);
lean_dec_ref(v_a_334_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1___redArg(lean_object* v_m_338_, lean_object* v_a_339_, lean_object* v_b_340_){
_start:
{
lean_object* v_size_341_; lean_object* v_buckets_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_388_; 
v_size_341_ = lean_ctor_get(v_m_338_, 0);
v_buckets_342_ = lean_ctor_get(v_m_338_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v_m_338_);
if (v_isSharedCheck_388_ == 0)
{
v___x_344_ = v_m_338_;
v_isShared_345_ = v_isSharedCheck_388_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_buckets_342_);
lean_inc(v_size_341_);
lean_dec(v_m_338_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_388_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; uint64_t v___x_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v_fold_353_; uint64_t v___x_354_; uint64_t v___x_355_; uint64_t v___x_356_; size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; size_t v___x_361_; lean_object* v_bkt_362_; uint8_t v___x_363_; 
v___x_346_ = lean_array_get_size(v_buckets_342_);
v___x_347_ = lean_ptr_addr(v_a_339_);
v___x_348_ = ((size_t)3ULL);
v___x_349_ = lean_usize_shift_right(v___x_347_, v___x_348_);
v___x_350_ = lean_usize_to_uint64(v___x_349_);
v___x_351_ = 32ULL;
v___x_352_ = lean_uint64_shift_right(v___x_350_, v___x_351_);
v_fold_353_ = lean_uint64_xor(v___x_350_, v___x_352_);
v___x_354_ = 16ULL;
v___x_355_ = lean_uint64_shift_right(v_fold_353_, v___x_354_);
v___x_356_ = lean_uint64_xor(v_fold_353_, v___x_355_);
v___x_357_ = lean_uint64_to_usize(v___x_356_);
v___x_358_ = lean_usize_of_nat(v___x_346_);
v___x_359_ = ((size_t)1ULL);
v___x_360_ = lean_usize_sub(v___x_358_, v___x_359_);
v___x_361_ = lean_usize_land(v___x_357_, v___x_360_);
v_bkt_362_ = lean_array_uget_borrowed(v_buckets_342_, v___x_361_);
v___x_363_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4___redArg(v_a_339_, v_bkt_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v_size_x27_365_; lean_object* v___x_366_; lean_object* v_buckets_x27_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_364_ = lean_unsigned_to_nat(1u);
v_size_x27_365_ = lean_nat_add(v_size_341_, v___x_364_);
lean_dec(v_size_341_);
lean_inc(v_bkt_362_);
v___x_366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_366_, 0, v_a_339_);
lean_ctor_set(v___x_366_, 1, v_b_340_);
lean_ctor_set(v___x_366_, 2, v_bkt_362_);
v_buckets_x27_367_ = lean_array_uset(v_buckets_342_, v___x_361_, v___x_366_);
v___x_368_ = lean_unsigned_to_nat(4u);
v___x_369_ = lean_nat_mul(v_size_x27_365_, v___x_368_);
v___x_370_ = lean_unsigned_to_nat(3u);
v___x_371_ = lean_nat_div(v___x_369_, v___x_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_array_get_size(v_buckets_x27_367_);
v___x_373_ = lean_nat_dec_le(v___x_371_, v___x_372_);
lean_dec(v___x_371_);
if (v___x_373_ == 0)
{
lean_object* v_val_374_; lean_object* v___x_376_; 
v_val_374_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5___redArg(v_buckets_x27_367_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v_val_374_);
lean_ctor_set(v___x_344_, 0, v_size_x27_365_);
v___x_376_ = v___x_344_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_size_x27_365_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_val_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_object* v___x_379_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v_buckets_x27_367_);
lean_ctor_set(v___x_344_, 0, v_size_x27_365_);
v___x_379_ = v___x_344_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_size_x27_365_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_buckets_x27_367_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
lean_object* v___x_381_; lean_object* v_buckets_x27_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
lean_inc(v_bkt_362_);
v___x_381_ = lean_box(0);
v_buckets_x27_382_ = lean_array_uset(v_buckets_342_, v___x_361_, v___x_381_);
v___x_383_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__6___redArg(v_a_339_, v_b_340_, v_bkt_362_);
v___x_384_ = lean_array_uset(v_buckets_x27_382_, v___x_361_, v___x_383_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v___x_384_);
v___x_386_ = v___x_344_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_size_341_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort(lean_object* v_type_389_, lean_object* v_level_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_Sym_shareCommonInc(v_type_389_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_431_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_431_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_431_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_431_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v_sorts_405_; lean_object* v_sortIds_406_; lean_object* v_nextSortId_407_; lean_object* v_elements_408_; lean_object* v_preds_409_; lean_object* v_groundFacts_410_; lean_object* v_quantifiedFacts_411_; lean_object* v_remainingHyps_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_430_; 
v___x_404_ = lean_st_ref_take(v_a_391_);
v_sorts_405_ = lean_ctor_get(v___x_404_, 0);
v_sortIds_406_ = lean_ctor_get(v___x_404_, 1);
v_nextSortId_407_ = lean_ctor_get(v___x_404_, 2);
v_elements_408_ = lean_ctor_get(v___x_404_, 3);
v_preds_409_ = lean_ctor_get(v___x_404_, 4);
v_groundFacts_410_ = lean_ctor_get(v___x_404_, 5);
v_quantifiedFacts_411_ = lean_ctor_get(v___x_404_, 6);
v_remainingHyps_412_ = lean_ctor_get(v___x_404_, 7);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_430_ == 0)
{
v___x_414_ = v___x_404_;
v_isShared_415_ = v_isSharedCheck_430_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_remainingHyps_412_);
lean_inc(v_quantifiedFacts_411_);
lean_inc(v_groundFacts_410_);
lean_inc(v_preds_409_);
lean_inc(v_elements_408_);
lean_inc(v_nextSortId_407_);
lean_inc(v_sortIds_406_);
lean_inc(v_sorts_405_);
lean_dec(v___x_404_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_430_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_416_ = lean_box(0);
v___x_417_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__3));
lean_inc(v_a_400_);
v___x_418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_418_, 0, v_a_400_);
lean_ctor_set(v___x_418_, 1, v_level_390_);
lean_ctor_set(v___x_418_, 2, v___x_417_);
lean_inc_n(v_nextSortId_407_, 2);
v___x_419_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0___redArg(v_sorts_405_, v_nextSortId_407_, v___x_418_);
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1___redArg(v_sortIds_406_, v_a_400_, v_nextSortId_407_);
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v_nextSortId_407_, v___x_421_);
lean_dec(v_nextSortId_407_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 2, v___x_422_);
lean_ctor_set(v___x_414_, 1, v___x_420_);
lean_ctor_set(v___x_414_, 0, v___x_419_);
v___x_424_ = v___x_414_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v_elements_408_);
lean_ctor_set(v_reuseFailAlloc_429_, 4, v_preds_409_);
lean_ctor_set(v_reuseFailAlloc_429_, 5, v_groundFacts_410_);
lean_ctor_set(v_reuseFailAlloc_429_, 6, v_quantifiedFacts_411_);
lean_ctor_set(v_reuseFailAlloc_429_, 7, v_remainingHyps_412_);
v___x_424_ = v_reuseFailAlloc_429_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_st_ref_put(v_a_391_, v___x_424_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_416_);
v___x_427_ = v___x_402_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_416_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec(v_level_390_);
v_a_432_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_399_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_399_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort___boxed(lean_object* v_type_440_, lean_object* v_level_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort(v_type_440_, v_level_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0(lean_object* v_00_u03b2_451_, lean_object* v_m_452_, lean_object* v_a_453_, lean_object* v_b_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0___redArg(v_m_452_, v_a_453_, v_b_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1(lean_object* v_00_u03b2_456_, lean_object* v_m_457_, lean_object* v_a_458_, lean_object* v_b_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1___redArg(v_m_457_, v_a_458_, v_b_459_);
return v___x_460_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0(lean_object* v_00_u03b2_461_, lean_object* v_a_462_, lean_object* v_x_463_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___redArg(v_a_462_, v_x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___boxed(lean_object* v_00_u03b2_465_, lean_object* v_a_466_, lean_object* v_x_467_){
_start:
{
uint8_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0(v_00_u03b2_465_, v_a_466_, v_x_467_);
lean_dec(v_x_467_);
lean_dec(v_a_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1(lean_object* v_00_u03b2_470_, lean_object* v_data_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1___redArg(v_data_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__2(lean_object* v_00_u03b2_473_, lean_object* v_a_474_, lean_object* v_b_475_, lean_object* v_x_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__2___redArg(v_a_474_, v_b_475_, v_x_476_);
return v___x_477_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4(lean_object* v_00_u03b2_478_, lean_object* v_a_479_, lean_object* v_x_480_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4___redArg(v_a_479_, v_x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4___boxed(lean_object* v_00_u03b2_482_, lean_object* v_a_483_, lean_object* v_x_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4(v_00_u03b2_482_, v_a_483_, v_x_484_);
lean_dec(v_x_484_);
lean_dec_ref(v_a_483_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5(lean_object* v_00_u03b2_487_, lean_object* v_data_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5___redArg(v_data_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__6(lean_object* v_00_u03b2_490_, lean_object* v_a_491_, lean_object* v_b_492_, lean_object* v_x_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__6___redArg(v_a_491_, v_b_492_, v_x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_495_, lean_object* v_i_496_, lean_object* v_source_497_, lean_object* v_target_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2___redArg(v_i_496_, v_source_497_, v_target_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7(lean_object* v_00_u03b2_500_, lean_object* v_i_501_, lean_object* v_source_502_, lean_object* v_target_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7___redArg(v_i_501_, v_source_502_, v_target_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2_spec__4___redArg(v_x_506_, v_x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7_spec__9___redArg(v_x_510_, v_x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement_spec__0_spec__0(lean_object* v_elem_513_, lean_object* v_a_514_, lean_object* v_x_515_){
_start:
{
if (lean_obj_tag(v_x_515_) == 0)
{
lean_dec(v_a_514_);
lean_dec_ref(v_elem_513_);
return v_x_515_;
}
else
{
lean_object* v_key_516_; lean_object* v_value_517_; lean_object* v_tail_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_541_; 
v_key_516_ = lean_ctor_get(v_x_515_, 0);
v_value_517_ = lean_ctor_get(v_x_515_, 1);
v_tail_518_ = lean_ctor_get(v_x_515_, 2);
v_isSharedCheck_541_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_541_ == 0)
{
v___x_520_ = v_x_515_;
v_isShared_521_ = v_isSharedCheck_541_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_tail_518_);
lean_inc(v_value_517_);
lean_inc(v_key_516_);
lean_dec(v_x_515_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_541_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
uint8_t v___x_522_; 
v___x_522_ = lean_nat_dec_eq(v_key_516_, v_a_514_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement_spec__0_spec__0(v_elem_513_, v_a_514_, v_tail_518_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 2, v___x_523_);
v___x_525_ = v___x_520_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_key_516_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_value_517_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
else
{
lean_object* v_type_527_; lean_object* v_level_528_; lean_object* v_elements_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_key_516_);
v_type_527_ = lean_ctor_get(v_value_517_, 0);
v_level_528_ = lean_ctor_get(v_value_517_, 1);
v_elements_529_ = lean_ctor_get(v_value_517_, 2);
v_isSharedCheck_540_ = !lean_is_exclusive(v_value_517_);
if (v_isSharedCheck_540_ == 0)
{
v___x_531_ = v_value_517_;
v_isShared_532_ = v_isSharedCheck_540_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_elements_529_);
lean_inc(v_level_528_);
lean_inc(v_type_527_);
lean_dec(v_value_517_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_540_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = lean_array_push(v_elements_529_, v_elem_513_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 2, v___x_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_type_527_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_level_528_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v___x_533_);
v___x_535_ = v_reuseFailAlloc_539_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_537_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v___x_535_);
lean_ctor_set(v___x_520_, 0, v_a_514_);
v___x_537_ = v___x_520_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_514_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_tail_518_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement_spec__0(lean_object* v_elem_542_, lean_object* v_m_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_size_545_; lean_object* v_buckets_546_; lean_object* v___x_547_; uint64_t v___x_548_; uint64_t v___x_549_; uint64_t v___x_550_; uint64_t v_fold_551_; uint64_t v___x_552_; uint64_t v___x_553_; uint64_t v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; lean_object* v_bucket_560_; uint8_t v___x_561_; 
v_size_545_ = lean_ctor_get(v_m_543_, 0);
v_buckets_546_ = lean_ctor_get(v_m_543_, 1);
v___x_547_ = lean_array_get_size(v_buckets_546_);
v___x_548_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_a_544_);
v___x_549_ = 32ULL;
v___x_550_ = lean_uint64_shift_right(v___x_548_, v___x_549_);
v_fold_551_ = lean_uint64_xor(v___x_548_, v___x_550_);
v___x_552_ = 16ULL;
v___x_553_ = lean_uint64_shift_right(v_fold_551_, v___x_552_);
v___x_554_ = lean_uint64_xor(v_fold_551_, v___x_553_);
v___x_555_ = lean_uint64_to_usize(v___x_554_);
v___x_556_ = lean_usize_of_nat(v___x_547_);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_sub(v___x_556_, v___x_557_);
v___x_559_ = lean_usize_land(v___x_555_, v___x_558_);
v_bucket_560_ = lean_array_uget_borrowed(v_buckets_546_, v___x_559_);
v___x_561_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___redArg(v_a_544_, v_bucket_560_);
if (v___x_561_ == 0)
{
lean_dec(v_a_544_);
lean_dec_ref(v_elem_542_);
return v_m_543_;
}
else
{
lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_572_; 
lean_inc(v_bucket_560_);
lean_inc_ref(v_buckets_546_);
lean_inc(v_size_545_);
v_isSharedCheck_572_ = !lean_is_exclusive(v_m_543_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; lean_object* v_unused_574_; 
v_unused_573_ = lean_ctor_get(v_m_543_, 1);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_m_543_, 0);
lean_dec(v_unused_574_);
v___x_563_ = v_m_543_;
v_isShared_564_ = v_isSharedCheck_572_;
goto v_resetjp_562_;
}
else
{
lean_dec(v_m_543_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_572_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v_buckets_566_; lean_object* v_bucket_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_565_ = lean_box(0);
v_buckets_566_ = lean_array_uset(v_buckets_546_, v___x_559_, v___x_565_);
v_bucket_567_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement_spec__0_spec__0(v_elem_542_, v_a_544_, v_bucket_560_);
v___x_568_ = lean_array_uset(v_buckets_566_, v___x_559_, v_bucket_567_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___x_568_);
v___x_570_ = v___x_563_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_size_545_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg(lean_object* v_elem_575_, lean_object* v_sort_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_579_; lean_object* v_sorts_580_; lean_object* v_sortIds_581_; lean_object* v_nextSortId_582_; lean_object* v_elements_583_; lean_object* v_preds_584_; lean_object* v_groundFacts_585_; lean_object* v_quantifiedFacts_586_; lean_object* v_remainingHyps_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_599_; 
v___x_579_ = lean_st_ref_take(v_a_577_);
v_sorts_580_ = lean_ctor_get(v___x_579_, 0);
v_sortIds_581_ = lean_ctor_get(v___x_579_, 1);
v_nextSortId_582_ = lean_ctor_get(v___x_579_, 2);
v_elements_583_ = lean_ctor_get(v___x_579_, 3);
v_preds_584_ = lean_ctor_get(v___x_579_, 4);
v_groundFacts_585_ = lean_ctor_get(v___x_579_, 5);
v_quantifiedFacts_586_ = lean_ctor_get(v___x_579_, 6);
v_remainingHyps_587_ = lean_ctor_get(v___x_579_, 7);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_599_ == 0)
{
v___x_589_ = v___x_579_;
v_isShared_590_ = v_isSharedCheck_599_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_remainingHyps_587_);
lean_inc(v_quantifiedFacts_586_);
lean_inc(v_groundFacts_585_);
lean_inc(v_preds_584_);
lean_inc(v_elements_583_);
lean_inc(v_nextSortId_582_);
lean_inc(v_sortIds_581_);
lean_inc(v_sorts_580_);
lean_dec(v___x_579_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_599_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_591_ = lean_box(0);
lean_inc(v_sort_576_);
lean_inc_ref(v_elem_575_);
v___x_592_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement_spec__0(v_elem_575_, v_sorts_580_, v_sort_576_);
v___x_593_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1___redArg(v_elements_583_, v_elem_575_, v_sort_576_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 3, v___x_593_);
lean_ctor_set(v___x_589_, 0, v___x_592_);
v___x_595_ = v___x_589_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_sortIds_581_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_nextSortId_582_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_preds_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 5, v_groundFacts_585_);
lean_ctor_set(v_reuseFailAlloc_598_, 6, v_quantifiedFacts_586_);
lean_ctor_set(v_reuseFailAlloc_598_, 7, v_remainingHyps_587_);
v___x_595_ = v_reuseFailAlloc_598_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_st_ref_put(v_a_577_, v___x_595_);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_591_);
return v___x_597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg___boxed(lean_object* v_elem_600_, lean_object* v_sort_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg(v_elem_600_, v_sort_601_, v_a_602_);
lean_dec(v_a_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement(lean_object* v_elem_605_, lean_object* v_sort_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg(v_elem_605_, v_sort_606_, v_a_607_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___boxed(lean_object* v_elem_616_, lean_object* v_sort_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement(v_elem_616_, v_sort_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerPred(lean_object* v_pred_627_, lean_object* v_argumentSorts_628_, uint8_t v_encoding_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Meta_Sym_shareCommonInc(v_pred_627_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_666_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_666_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_666_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_666_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v_sorts_644_; lean_object* v_sortIds_645_; lean_object* v_nextSortId_646_; lean_object* v_elements_647_; lean_object* v_preds_648_; lean_object* v_groundFacts_649_; lean_object* v_quantifiedFacts_650_; lean_object* v_remainingHyps_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_665_; 
v___x_643_ = lean_st_ref_take(v_a_630_);
v_sorts_644_ = lean_ctor_get(v___x_643_, 0);
v_sortIds_645_ = lean_ctor_get(v___x_643_, 1);
v_nextSortId_646_ = lean_ctor_get(v___x_643_, 2);
v_elements_647_ = lean_ctor_get(v___x_643_, 3);
v_preds_648_ = lean_ctor_get(v___x_643_, 4);
v_groundFacts_649_ = lean_ctor_get(v___x_643_, 5);
v_quantifiedFacts_650_ = lean_ctor_get(v___x_643_, 6);
v_remainingHyps_651_ = lean_ctor_get(v___x_643_, 7);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_665_ == 0)
{
v___x_653_ = v___x_643_;
v_isShared_654_ = v_isSharedCheck_665_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_remainingHyps_651_);
lean_inc(v_quantifiedFacts_650_);
lean_inc(v_groundFacts_649_);
lean_inc(v_preds_648_);
lean_inc(v_elements_647_);
lean_inc(v_nextSortId_646_);
lean_inc(v_sortIds_645_);
lean_inc(v_sorts_644_);
lean_dec(v___x_643_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_665_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_655_ = lean_box(0);
v___x_656_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_656_, 0, v_argumentSorts_628_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*1, v_encoding_629_);
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1___redArg(v_preds_648_, v_a_639_, v___x_656_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 4, v___x_657_);
v___x_659_ = v___x_653_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_sorts_644_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_sortIds_645_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_nextSortId_646_);
lean_ctor_set(v_reuseFailAlloc_664_, 3, v_elements_647_);
lean_ctor_set(v_reuseFailAlloc_664_, 4, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_664_, 5, v_groundFacts_649_);
lean_ctor_set(v_reuseFailAlloc_664_, 6, v_quantifiedFacts_650_);
lean_ctor_set(v_reuseFailAlloc_664_, 7, v_remainingHyps_651_);
v___x_659_ = v_reuseFailAlloc_664_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = lean_st_ref_put(v_a_630_, v___x_659_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_655_);
v___x_662_ = v___x_641_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_655_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v_argumentSorts_628_);
v_a_667_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_638_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_638_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerPred___boxed(lean_object* v_pred_675_, lean_object* v_argumentSorts_676_, lean_object* v_encoding_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
uint8_t v_encoding_boxed_686_; lean_object* v_res_687_; 
v_encoding_boxed_686_ = lean_unbox(v_encoding_677_);
v_res_687_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerPred(v_pred_675_, v_argumentSorts_676_, v_encoding_boxed_686_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___redArg(lean_object* v_a_688_, lean_object* v_x_689_){
_start:
{
if (lean_obj_tag(v_x_689_) == 0)
{
lean_object* v___x_690_; 
v___x_690_ = lean_box(0);
return v___x_690_;
}
else
{
lean_object* v_key_691_; lean_object* v_value_692_; lean_object* v_tail_693_; size_t v___x_694_; size_t v___x_695_; uint8_t v___x_696_; 
v_key_691_ = lean_ctor_get(v_x_689_, 0);
v_value_692_ = lean_ctor_get(v_x_689_, 1);
v_tail_693_ = lean_ctor_get(v_x_689_, 2);
v___x_694_ = lean_ptr_addr(v_key_691_);
v___x_695_ = lean_ptr_addr(v_a_688_);
v___x_696_ = lean_usize_dec_eq(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
v_x_689_ = v_tail_693_;
goto _start;
}
else
{
lean_object* v___x_698_; 
lean_inc(v_value_692_);
v___x_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_698_, 0, v_value_692_);
return v___x_698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_699_, lean_object* v_x_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___redArg(v_a_699_, v_x_700_);
lean_dec(v_x_700_);
lean_dec_ref(v_a_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(lean_object* v_m_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_buckets_704_; lean_object* v___x_705_; size_t v___x_706_; size_t v___x_707_; size_t v___x_708_; uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v___x_711_; uint64_t v_fold_712_; uint64_t v___x_713_; uint64_t v___x_714_; uint64_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_buckets_704_ = lean_ctor_get(v_m_702_, 1);
v___x_705_ = lean_array_get_size(v_buckets_704_);
v___x_706_ = lean_ptr_addr(v_a_703_);
v___x_707_ = ((size_t)3ULL);
v___x_708_ = lean_usize_shift_right(v___x_706_, v___x_707_);
v___x_709_ = lean_usize_to_uint64(v___x_708_);
v___x_710_ = 32ULL;
v___x_711_ = lean_uint64_shift_right(v___x_709_, v___x_710_);
v_fold_712_ = lean_uint64_xor(v___x_709_, v___x_711_);
v___x_713_ = 16ULL;
v___x_714_ = lean_uint64_shift_right(v_fold_712_, v___x_713_);
v___x_715_ = lean_uint64_xor(v_fold_712_, v___x_714_);
v___x_716_ = lean_uint64_to_usize(v___x_715_);
v___x_717_ = lean_usize_of_nat(v___x_705_);
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_sub(v___x_717_, v___x_718_);
v___x_720_ = lean_usize_land(v___x_716_, v___x_719_);
v___x_721_ = lean_array_uget_borrowed(v_buckets_704_, v___x_720_);
v___x_722_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___redArg(v_a_703_, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg___boxed(lean_object* v_m_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_m_723_, v_a_724_);
lean_dec_ref(v_a_724_);
lean_dec_ref(v_m_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg(lean_object* v_type_727_, lean_object* v_acc_728_, lean_object* v_a_729_){
_start:
{
switch(lean_obj_tag(v_type_727_))
{
case 3:
{
lean_object* v_u_734_; 
v_u_734_ = lean_ctor_get(v_type_727_, 0);
if (lean_obj_tag(v_u_734_) == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_735_ = lean_array_get_size(v_acc_728_);
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_nat_dec_eq(v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_738_ = 0;
v___x_739_ = lean_box(v___x_738_);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v_acc_728_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec_ref(v_acc_728_);
v___x_743_ = lean_box(0);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
else
{
lean_dec_ref(v_acc_728_);
goto v___jp_731_;
}
}
case 4:
{
lean_object* v_declName_745_; 
v_declName_745_ = lean_ctor_get(v_type_727_, 0);
if (lean_obj_tag(v_declName_745_) == 1)
{
lean_object* v_pre_746_; 
v_pre_746_ = lean_ctor_get(v_declName_745_, 0);
if (lean_obj_tag(v_pre_746_) == 0)
{
lean_object* v_us_747_; lean_object* v_str_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_us_747_ = lean_ctor_get(v_type_727_, 1);
v_str_748_ = lean_ctor_get(v_declName_745_, 1);
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___closed__0));
v___x_750_ = lean_string_dec_eq(v_str_748_, v___x_749_);
if (v___x_750_ == 0)
{
lean_dec_ref(v_acc_728_);
goto v___jp_731_;
}
else
{
if (lean_obj_tag(v_us_747_) == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_751_ = lean_array_get_size(v_acc_728_);
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = lean_nat_dec_eq(v___x_751_, v___x_752_);
if (v___x_753_ == 0)
{
uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_754_ = 1;
v___x_755_ = lean_box(v___x_754_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v_acc_728_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; 
lean_dec_ref(v_acc_728_);
v___x_759_ = lean_box(0);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
}
else
{
lean_dec_ref(v_acc_728_);
goto v___jp_731_;
}
}
}
else
{
lean_dec_ref(v_acc_728_);
goto v___jp_731_;
}
}
else
{
lean_dec_ref(v_acc_728_);
goto v___jp_731_;
}
}
case 7:
{
lean_object* v_binderType_761_; lean_object* v_body_762_; uint8_t v___x_763_; 
v_binderType_761_ = lean_ctor_get(v_type_727_, 1);
v_body_762_ = lean_ctor_get(v_type_727_, 2);
v___x_763_ = l_Lean_Expr_hasLooseBVars(v_body_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v_sortIds_765_; lean_object* v___x_766_; 
v___x_764_ = lean_st_ref_get(v_a_729_);
v_sortIds_765_ = lean_ctor_get(v___x_764_, 1);
lean_inc_ref(v_sortIds_765_);
lean_dec(v___x_764_);
v___x_766_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_sortIds_765_, v_binderType_761_);
lean_dec_ref(v_sortIds_765_);
if (lean_obj_tag(v___x_766_) == 1)
{
lean_object* v_val_767_; lean_object* v___x_768_; 
v_val_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_val_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = lean_array_push(v_acc_728_, v_val_767_);
v_type_727_ = v_body_762_;
v_acc_728_ = v___x_768_;
goto _start;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec(v___x_766_);
lean_dec_ref(v_acc_728_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec_ref(v_acc_728_);
v___x_772_ = lean_box(0);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
default: 
{
lean_dec_ref(v_acc_728_);
goto v___jp_731_;
}
}
v___jp_731_:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_box(0);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___boxed(lean_object* v_type_774_, lean_object* v_acc_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg(v_type_774_, v_acc_775_, v_a_776_);
lean_dec(v_a_776_);
lean_dec_ref(v_type_774_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go(lean_object* v_type_779_, lean_object* v_acc_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg(v_type_779_, v_acc_780_, v_a_781_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___boxed(lean_object* v_type_790_, lean_object* v_acc_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go(v_type_790_, v_acc_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec_ref(v_type_790_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0(lean_object* v_00_u03b2_801_, lean_object* v_m_802_, lean_object* v_a_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_m_802_, v_a_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_805_, lean_object* v_m_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0(v_00_u03b2_805_, v_m_806_, v_a_807_);
lean_dec_ref(v_a_807_);
lean_dec_ref(v_m_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0(lean_object* v_00_u03b2_809_, lean_object* v_a_810_, lean_object* v_x_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___redArg(v_a_810_, v_x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_813_, lean_object* v_a_814_, lean_object* v_x_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0(v_00_u03b2_813_, v_a_814_, v_x_815_);
lean_dec(v_x_815_);
lean_dec_ref(v_a_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg(lean_object* v_type_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg___closed__0));
v___x_823_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg(v_type_819_, v___x_822_, v_a_820_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg___boxed(lean_object* v_type_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg(v_type_824_, v_a_825_);
lean_dec(v_a_825_);
lean_dec_ref(v_type_824_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f(lean_object* v_type_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg(v_type_828_, v_a_829_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___boxed(lean_object* v_type_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f(v_type_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_type_838_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processLocalDecl(lean_object* v_decl_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = l_Lean_LocalDecl_isImplementationDetail(v_decl_848_);
if (v___x_860_ == 0)
{
uint8_t v___x_861_; 
v___x_861_ = l_Lean_LocalDecl_isLet(v_decl_848_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = l_Lean_LocalDecl_type(v_decl_848_);
v___x_863_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_862_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
if (lean_obj_tag(v_a_864_) == 3)
{
lean_object* v_u_915_; 
v_u_915_ = lean_ctor_get(v_a_864_, 0);
if (lean_obj_tag(v_u_915_) == 1)
{
lean_object* v_a_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
lean_inc_ref(v_u_915_);
lean_dec_ref_known(v_a_864_, 1);
v_a_916_ = lean_ctor_get(v_u_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v_u_915_, 1);
v___x_917_ = l_Lean_LocalDecl_toExpr(v_decl_848_);
v___x_918_ = l_Lean_Meta_Sym_shareCommonInc(v___x_917_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_920_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_918_, 1);
v___x_920_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort(v_a_919_, v_a_916_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
return v___x_920_;
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec(v_a_916_);
v_a_921_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_918_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_918_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
else
{
v___y_866_ = v_a_849_;
v___y_867_ = v_a_850_;
v___y_868_ = v_a_851_;
v___y_869_ = v_a_852_;
v___y_870_ = v_a_853_;
v___y_871_ = v_a_854_;
v___y_872_ = v_a_855_;
goto v___jp_865_;
}
}
else
{
v___y_866_ = v_a_849_;
v___y_867_ = v_a_850_;
v___y_868_ = v_a_851_;
v___y_869_ = v_a_852_;
v___y_870_ = v_a_853_;
v___y_871_ = v_a_854_;
v___y_872_ = v_a_855_;
goto v___jp_865_;
}
v___jp_865_:
{
lean_object* v___x_873_; lean_object* v_sortIds_874_; lean_object* v___x_875_; 
v___x_873_ = lean_st_ref_get(v___y_866_);
v_sortIds_874_ = lean_ctor_get(v___x_873_, 1);
lean_inc_ref(v_sortIds_874_);
lean_dec(v___x_873_);
v___x_875_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_sortIds_874_, v_a_864_);
lean_dec_ref(v_sortIds_874_);
if (lean_obj_tag(v___x_875_) == 1)
{
lean_object* v_val_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec(v_a_864_);
v_val_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_val_876_);
lean_dec_ref_known(v___x_875_, 1);
v___x_877_ = l_Lean_LocalDecl_toExpr(v_decl_848_);
v___x_878_ = l_Lean_Meta_Sym_shareCommonInc(v___x_877_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_880_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
v___x_880_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg(v_a_879_, v_val_876_, v___y_866_);
return v___x_880_;
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_val_876_);
v_a_881_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_878_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_878_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v___x_889_; lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_914_; 
lean_dec(v___x_875_);
v___x_889_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg(v_a_864_, v___y_866_);
lean_dec(v_a_864_);
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_914_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_914_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_914_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
if (lean_obj_tag(v_a_890_) == 1)
{
lean_object* v_val_894_; lean_object* v_fst_895_; lean_object* v_snd_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
lean_del_object(v___x_892_);
v_val_894_ = lean_ctor_get(v_a_890_, 0);
lean_inc(v_val_894_);
lean_dec_ref_known(v_a_890_, 1);
v_fst_895_ = lean_ctor_get(v_val_894_, 0);
lean_inc(v_fst_895_);
v_snd_896_ = lean_ctor_get(v_val_894_, 1);
lean_inc(v_snd_896_);
lean_dec(v_val_894_);
v___x_897_ = l_Lean_LocalDecl_toExpr(v_decl_848_);
v___x_898_ = l_Lean_Meta_Sym_shareCommonInc(v___x_897_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; uint8_t v___x_900_; lean_object* v___x_901_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
v___x_900_ = lean_unbox(v_snd_896_);
lean_dec(v_snd_896_);
v___x_901_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerPred(v_a_899_, v_fst_895_, v___x_900_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
return v___x_901_;
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_snd_896_);
lean_dec(v_fst_895_);
v_a_902_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_898_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_898_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
lean_object* v___x_910_; lean_object* v___x_912_; 
lean_dec(v_a_890_);
lean_dec_ref(v_decl_848_);
v___x_910_ = lean_box(0);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_910_);
v___x_912_ = v___x_892_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec_ref(v_decl_848_);
v_a_929_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_863_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_863_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_dec_ref(v_decl_848_);
goto v___jp_857_;
}
}
else
{
lean_dec_ref(v_decl_848_);
goto v___jp_857_;
}
v___jp_857_:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_box(0);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processLocalDecl___boxed(lean_object* v_decl_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processLocalDecl(v_decl_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort___redArg(lean_object* v_a_947_){
_start:
{
lean_object* v___x_949_; lean_object* v_cache_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_961_; 
v___x_949_ = lean_st_ref_take(v_a_947_);
v_cache_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_961_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_961_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_cache_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_961_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; uint8_t v___x_955_; lean_object* v___x_957_; 
v___x_954_ = lean_box(0);
v___x_955_ = 1;
if (v_isShared_953_ == 0)
{
v___x_957_ = v___x_952_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_cache_950_);
v___x_957_ = v_reuseFailAlloc_960_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_ctor_set_uint8(v___x_957_, sizeof(void*)*1, v___x_955_);
v___x_958_ = lean_st_ref_put(v_a_947_, v___x_957_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_954_);
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort___redArg___boxed(lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort___redArg(v_a_962_);
lean_dec(v_a_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort(lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v___x_975_; lean_object* v_cache_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_987_; 
v___x_975_ = lean_st_ref_take(v_a_966_);
v_cache_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_987_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_987_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_cache_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_987_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___x_983_; 
v___x_980_ = lean_box(0);
v___x_981_ = 1;
if (v_isShared_979_ == 0)
{
v___x_983_ = v___x_978_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_cache_976_);
v___x_983_ = v_reuseFailAlloc_986_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*1, v___x_981_);
v___x_984_ = lean_st_ref_put(v_a_966_, v___x_983_);
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_980_);
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort___boxed(lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort(v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(lean_object* v_e_999_, lean_object* v_depth_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
if (lean_obj_tag(v_e_999_) == 0)
{
lean_object* v_deBruijnIndex_1005_; uint8_t v___x_1006_; 
v_deBruijnIndex_1005_ = lean_ctor_get(v_e_999_, 0);
v___x_1006_ = lean_nat_dec_lt(v_deBruijnIndex_1005_, v_depth_1000_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1007_ = lean_nat_sub(v_deBruijnIndex_1005_, v_depth_1000_);
v___x_1008_ = lean_array_get_size(v_a_1001_);
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_nat_sub(v___x_1008_, v___x_1009_);
v___x_1011_ = lean_nat_sub(v___x_1010_, v___x_1007_);
lean_dec(v___x_1007_);
lean_dec(v___x_1010_);
v___x_1012_ = lean_nat_dec_lt(v___x_1011_, v___x_1008_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec(v___x_1011_);
v___x_1013_ = lean_box(0);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_array_fget_borrowed(v_a_1001_, v___x_1011_);
lean_dec(v___x_1011_);
lean_inc(v___x_1015_);
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
}
else
{
lean_object* v___x_1020_; lean_object* v_elements_1021_; lean_object* v___x_1022_; 
v___x_1020_ = lean_st_ref_get(v_a_1003_);
v_elements_1021_ = lean_ctor_get(v___x_1020_, 3);
lean_inc_ref(v_elements_1021_);
lean_dec(v___x_1020_);
v___x_1022_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_elements_1021_, v_e_999_);
lean_dec_ref(v_elements_1021_);
if (lean_obj_tag(v___x_1022_) == 1)
{
lean_object* v___x_1023_; lean_object* v_cache_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1034_; 
v___x_1023_ = lean_st_ref_take(v_a_1002_);
v_cache_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_cache_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
uint8_t v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = 1;
if (v_isShared_1027_ == 0)
{
v___x_1030_ = v___x_1026_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_cache_1024_);
v___x_1030_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*1, v___x_1028_);
v___x_1031_ = lean_st_ref_put(v_a_1002_, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1022_);
return v___x_1032_;
}
}
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
lean_dec(v___x_1022_);
v___x_1035_ = lean_box(0);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg___boxed(lean_object* v_e_1037_, lean_object* v_depth_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(v_e_1037_, v_depth_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_depth_1038_);
lean_dec_ref(v_e_1037_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm(lean_object* v_e_1044_, lean_object* v_depth_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(v_e_1044_, v_depth_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___boxed(lean_object* v_e_1057_, lean_object* v_depth_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm(v_e_1057_, v_depth_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_depth_1058_);
lean_dec_ref(v_e_1057_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___redArg(lean_object* v_00_u03b1_1070_, lean_object* v_lhs_1071_, lean_object* v_rhs_1072_, lean_object* v_depth_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1078_; lean_object* v_sortIds_1079_; lean_object* v___x_1080_; 
v___x_1078_ = lean_st_ref_get(v_a_1076_);
v_sortIds_1079_ = lean_ctor_get(v___x_1078_, 1);
lean_inc_ref(v_sortIds_1079_);
lean_dec(v___x_1078_);
v___x_1080_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_sortIds_1079_, v_00_u03b1_1070_);
lean_dec_ref(v_sortIds_1079_);
if (lean_obj_tag(v___x_1080_) == 1)
{
lean_object* v_val_1081_; lean_object* v___x_1082_; lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1115_; 
v_val_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_val_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(v_lhs_1071_, v_depth_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1115_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1115_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
if (lean_obj_tag(v_a_1083_) == 1)
{
lean_object* v_val_1087_; lean_object* v___x_1088_; lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1109_; 
lean_del_object(v___x_1085_);
v_val_1087_ = lean_ctor_get(v_a_1083_, 0);
lean_inc(v_val_1087_);
lean_dec_ref_known(v_a_1083_, 1);
v___x_1088_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(v_rhs_1072_, v_depth_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1109_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1109_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
if (lean_obj_tag(v_a_1089_) == 1)
{
lean_object* v_val_1093_; uint8_t v___x_1094_; 
v_val_1093_ = lean_ctor_get(v_a_1089_, 0);
lean_inc(v_val_1093_);
lean_dec_ref_known(v_a_1089_, 1);
v___x_1094_ = lean_nat_dec_eq(v_val_1087_, v_val_1081_);
lean_dec(v_val_1087_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
lean_dec(v_val_1093_);
lean_dec(v_val_1081_);
v___x_1095_ = lean_box(v___x_1094_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1095_);
v___x_1097_ = v___x_1091_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
else
{
uint8_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1099_ = lean_nat_dec_eq(v_val_1093_, v_val_1081_);
lean_dec(v_val_1081_);
lean_dec(v_val_1093_);
v___x_1100_ = lean_box(v___x_1099_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1100_);
v___x_1102_ = v___x_1091_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
else
{
uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
lean_dec(v_a_1089_);
lean_dec(v_val_1087_);
lean_dec(v_val_1081_);
v___x_1104_ = 0;
v___x_1105_ = lean_box(v___x_1104_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1105_);
v___x_1107_ = v___x_1091_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
lean_dec(v_a_1083_);
lean_dec(v_val_1081_);
v___x_1110_ = 0;
v___x_1111_ = lean_box(v___x_1110_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1111_);
v___x_1113_ = v___x_1085_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
uint8_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec(v___x_1080_);
v___x_1116_ = 0;
v___x_1117_ = lean_box(v___x_1116_);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___redArg___boxed(lean_object* v_00_u03b1_1119_, lean_object* v_lhs_1120_, lean_object* v_rhs_1121_, lean_object* v_depth_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___redArg(v_00_u03b1_1119_, v_lhs_1120_, v_rhs_1121_, v_depth_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_depth_1122_);
lean_dec_ref(v_rhs_1121_);
lean_dec_ref(v_lhs_1120_);
lean_dec_ref(v_00_u03b1_1119_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq(lean_object* v_00_u03b1_1128_, lean_object* v_lhs_1129_, lean_object* v_rhs_1130_, lean_object* v_depth_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___redArg(v_00_u03b1_1128_, v_lhs_1129_, v_rhs_1130_, v_depth_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___boxed(lean_object* v_00_u03b1_1143_, lean_object* v_lhs_1144_, lean_object* v_rhs_1145_, lean_object* v_depth_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq(v_00_u03b1_1143_, v_lhs_1144_, v_rhs_1145_, v_depth_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_depth_1146_);
lean_dec_ref(v_rhs_1145_);
lean_dec_ref(v_lhs_1144_);
lean_dec_ref(v_00_u03b1_1143_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg(lean_object* v_depth_1161_, lean_object* v_as_1162_, size_t v_sz_1163_, size_t v_i_1164_, lean_object* v_b_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_usize_dec_lt(v_i_1164_, v_sz_1163_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_b_1165_);
return v___x_1171_;
}
else
{
lean_object* v_snd_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1235_; 
v_snd_1172_ = lean_ctor_get(v_b_1165_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_b_1165_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v_b_1165_, 0);
lean_dec(v_unused_1236_);
v___x_1174_ = v_b_1165_;
v_isShared_1175_ = v_isSharedCheck_1235_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_snd_1172_);
lean_dec(v_b_1165_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1235_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_array_1176_; lean_object* v_start_1177_; lean_object* v_stop_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v_array_1176_ = lean_ctor_get(v_snd_1172_, 0);
v_start_1177_ = lean_ctor_get(v_snd_1172_, 1);
v_stop_1178_ = lean_ctor_get(v_snd_1172_, 2);
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_nat_dec_lt(v_start_1177_, v_stop_1178_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1182_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1179_);
v___x_1182_ = v___x_1174_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_snd_1172_);
v___x_1182_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
else
{
lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1231_; 
lean_inc(v_stop_1178_);
lean_inc(v_start_1177_);
lean_inc_ref(v_array_1176_);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_snd_1172_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; lean_object* v_unused_1233_; lean_object* v_unused_1234_; 
v_unused_1232_ = lean_ctor_get(v_snd_1172_, 2);
lean_dec(v_unused_1232_);
v_unused_1233_ = lean_ctor_get(v_snd_1172_, 1);
lean_dec(v_unused_1233_);
v_unused_1234_ = lean_ctor_get(v_snd_1172_, 0);
lean_dec(v_unused_1234_);
v___x_1186_ = v_snd_1172_;
v_isShared_1187_ = v_isSharedCheck_1231_;
goto v_resetjp_1185_;
}
else
{
lean_dec(v_snd_1172_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1231_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v_a_1188_ = lean_array_uget_borrowed(v_as_1162_, v_i_1164_);
v___x_1189_ = lean_array_fget(v_array_1176_, v_start_1177_);
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = lean_nat_add(v_start_1177_, v___x_1190_);
lean_dec(v_start_1177_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v___x_1191_);
v___x_1193_ = v___x_1186_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_array_1176_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_stop_1178_);
v___x_1193_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; 
v___x_1194_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(v_a_1188_, v_depth_1161_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1221_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1221_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1221_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
if (lean_obj_tag(v_a_1195_) == 1)
{
lean_object* v_val_1199_; uint8_t v___x_1200_; 
v_val_1199_ = lean_ctor_get(v_a_1195_, 0);
lean_inc(v_val_1199_);
lean_dec_ref_known(v_a_1195_, 1);
v___x_1200_ = lean_nat_dec_eq(v_val_1199_, v___x_1189_);
lean_dec(v___x_1189_);
lean_dec(v_val_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg___closed__0));
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v___x_1193_);
lean_ctor_set(v___x_1174_, 0, v___x_1201_);
v___x_1203_ = v___x_1174_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1193_);
v___x_1203_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1203_);
v___x_1205_ = v___x_1197_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
else
{
lean_object* v___x_1209_; 
lean_del_object(v___x_1197_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v___x_1193_);
lean_ctor_set(v___x_1174_, 0, v___x_1179_);
v___x_1209_ = v___x_1174_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___x_1193_);
v___x_1209_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
size_t v___x_1210_; size_t v___x_1211_; 
v___x_1210_ = ((size_t)1ULL);
v___x_1211_ = lean_usize_add(v_i_1164_, v___x_1210_);
v_i_1164_ = v___x_1211_;
v_b_1165_ = v___x_1209_;
goto _start;
}
}
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
lean_dec(v_a_1195_);
lean_dec(v___x_1189_);
v___x_1214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg___closed__0));
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v___x_1193_);
lean_ctor_set(v___x_1174_, 0, v___x_1214_);
v___x_1216_ = v___x_1174_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v___x_1193_);
v___x_1216_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1218_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1216_);
v___x_1218_ = v___x_1197_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec_ref(v___x_1193_);
lean_dec(v___x_1189_);
lean_del_object(v___x_1174_);
v_a_1222_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1194_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1194_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg___boxed(lean_object* v_depth_1237_, lean_object* v_as_1238_, lean_object* v_sz_1239_, lean_object* v_i_1240_, lean_object* v_b_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
size_t v_sz_boxed_1246_; size_t v_i_boxed_1247_; lean_object* v_res_1248_; 
v_sz_boxed_1246_ = lean_unbox_usize(v_sz_1239_);
lean_dec(v_sz_1239_);
v_i_boxed_1247_ = lean_unbox_usize(v_i_1240_);
lean_dec(v_i_1240_);
v_res_1248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg(v_depth_1237_, v_as_1238_, v_sz_boxed_1246_, v_i_boxed_1247_, v_b_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec_ref(v_as_1238_);
lean_dec(v_depth_1237_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__1(lean_object* v_depth_1249_, lean_object* v_x_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
if (lean_obj_tag(v_x_1250_) == 5)
{
lean_object* v_fn_1263_; lean_object* v_arg_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_fn_1263_ = lean_ctor_get(v_x_1250_, 0);
lean_inc_ref(v_fn_1263_);
v_arg_1264_ = lean_ctor_get(v_x_1250_, 1);
lean_inc_ref(v_arg_1264_);
lean_dec_ref_known(v_x_1250_, 2);
v___x_1265_ = lean_array_set(v_x_1251_, v_x_1252_, v_arg_1264_);
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_nat_sub(v_x_1252_, v___x_1266_);
lean_dec(v_x_1252_);
v_x_1250_ = v_fn_1263_;
v_x_1251_ = v___x_1265_;
v_x_1252_ = v___x_1267_;
goto _start;
}
else
{
lean_object* v___x_1269_; lean_object* v_preds_1270_; lean_object* v___x_1271_; 
lean_dec(v_x_1252_);
v___x_1269_ = lean_st_ref_get(v___y_1255_);
v_preds_1270_ = lean_ctor_get(v___x_1269_, 4);
lean_inc_ref(v_preds_1270_);
lean_dec(v___x_1269_);
v___x_1271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_preds_1270_, v_x_1250_);
lean_dec_ref(v_x_1250_);
lean_dec_ref(v_preds_1270_);
if (lean_obj_tag(v___x_1271_) == 1)
{
lean_object* v_val_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1323_; 
v_val_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1323_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_val_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1323_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v_argumentSorts_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_argumentSorts_1276_ = lean_ctor_get(v_val_1272_, 0);
lean_inc_ref(v_argumentSorts_1276_);
lean_dec(v_val_1272_);
v___x_1277_ = lean_array_get_size(v_x_1251_);
v___x_1278_ = lean_array_get_size(v_argumentSorts_1276_);
v___x_1279_ = lean_nat_dec_eq(v___x_1277_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
lean_dec_ref(v_argumentSorts_1276_);
lean_dec_ref(v_x_1251_);
v___x_1280_ = lean_box(v___x_1279_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set_tag(v___x_1274_, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1280_);
v___x_1282_ = v___x_1274_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; size_t v_sz_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
lean_del_object(v___x_1274_);
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = l_Array_toSubarray___redArg(v_argumentSorts_1276_, v___x_1284_, v___x_1278_);
v___x_1286_ = lean_box(0);
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
lean_ctor_set(v___x_1287_, 1, v___x_1285_);
v_sz_1288_ = lean_array_size(v_x_1251_);
v___x_1289_ = ((size_t)0ULL);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg(v_depth_1249_, v_x_1251_, v_sz_1288_, v___x_1289_, v___x_1287_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec_ref(v_x_1251_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1314_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1314_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1314_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_fst_1295_; 
v_fst_1295_ = lean_ctor_get(v_a_1291_, 0);
lean_inc(v_fst_1295_);
lean_dec(v_a_1291_);
if (lean_obj_tag(v_fst_1295_) == 0)
{
lean_object* v___x_1296_; lean_object* v_cache_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1309_; 
v___x_1296_ = lean_st_ref_take(v___y_1254_);
v_cache_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1309_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_cache_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1309_;
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
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_cache_1297_);
v___x_1302_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
lean_ctor_set_uint8(v___x_1302_, sizeof(void*)*1, v___x_1279_);
v___x_1303_ = lean_st_ref_put(v___y_1254_, v___x_1302_);
v___x_1304_ = lean_box(v___x_1279_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1304_);
v___x_1306_ = v___x_1293_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
else
{
lean_object* v_val_1310_; lean_object* v___x_1312_; 
v_val_1310_ = lean_ctor_get(v_fst_1295_, 0);
lean_inc(v_val_1310_);
lean_dec_ref_known(v_fst_1295_, 1);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v_val_1310_);
v___x_1312_ = v___x_1293_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_val_1310_);
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
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
v_a_1315_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1290_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1290_);
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
}
}
else
{
uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec(v___x_1271_);
lean_dec_ref(v_x_1251_);
v___x_1324_ = 0;
v___x_1325_ = lean_box(v___x_1324_);
v___x_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__1___boxed(lean_object* v_depth_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__1(v_depth_1327_, v_x_1328_, v_x_1329_, v_x_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v_depth_1327_);
return v_res_1341_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp___closed__0(void){
_start:
{
lean_object* v___x_1342_; lean_object* v_dummy_1343_; 
v___x_1342_ = lean_box(0);
v_dummy_1343_ = l_Lean_Expr_sort___override(v___x_1342_);
return v_dummy_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp(lean_object* v_e_1344_, lean_object* v_depth_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_dummy_1356_; lean_object* v_nargs_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_dummy_1356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp___closed__0);
v_nargs_1357_ = l_Lean_Expr_getAppNumArgs(v_e_1344_);
lean_inc(v_nargs_1357_);
v___x_1358_ = lean_mk_array(v_nargs_1357_, v_dummy_1356_);
v___x_1359_ = lean_unsigned_to_nat(1u);
v___x_1360_ = lean_nat_sub(v_nargs_1357_, v___x_1359_);
lean_dec(v_nargs_1357_);
v___x_1361_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__1(v_depth_1345_, v_e_1344_, v___x_1358_, v___x_1360_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp___boxed(lean_object* v_e_1362_, lean_object* v_depth_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp(v_e_1362_, v_depth_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_depth_1363_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0(lean_object* v_depth_1375_, lean_object* v_as_1376_, size_t v_sz_1377_, size_t v_i_1378_, lean_object* v_b_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg(v_depth_1375_, v_as_1376_, v_sz_1377_, v_i_1378_, v_b_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___boxed(lean_object* v_depth_1391_, lean_object* v_as_1392_, lean_object* v_sz_1393_, lean_object* v_i_1394_, lean_object* v_b_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
size_t v_sz_boxed_1406_; size_t v_i_boxed_1407_; lean_object* v_res_1408_; 
v_sz_boxed_1406_ = lean_unbox_usize(v_sz_1393_);
lean_dec(v_sz_1393_);
v_i_boxed_1407_ = lean_unbox_usize(v_i_1394_);
lean_dec(v_i_1394_);
v_res_1408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0(v_depth_1391_, v_as_1392_, v_sz_boxed_1406_, v_i_boxed_1407_, v_b_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec_ref(v_as_1392_);
lean_dec(v_depth_1391_);
return v_res_1408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__2(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___f_1414_; 
v___x_1413_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_1414_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1414_, 0, v___x_1413_);
return v___f_1414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__3(void){
_start:
{
lean_object* v___f_1415_; lean_object* v___f_1416_; lean_object* v___f_1417_; 
v___f_1415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__2);
v___f_1416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___closed__0));
v___f_1417_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1417_, 0, v___f_1416_);
lean_closure_set(v___f_1417_, 1, v___f_1415_);
return v___f_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache(lean_object* v_e_1418_, lean_object* v_depth_1419_, lean_object* v_k_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v___f_1431_; lean_object* v___x_1432_; lean_object* v_cache_1433_; lean_object* v___f_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; uint8_t v___x_1437_; 
v___f_1431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__1));
v___x_1432_ = lean_st_ref_get(v_a_1422_);
v_cache_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc_ref(v_cache_1433_);
lean_dec(v___x_1432_);
v___f_1434_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__3);
lean_inc(v_depth_1419_);
lean_inc_ref(v_e_1418_);
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_e_1418_);
lean_ctor_set(v___x_1435_, 1, v_depth_1419_);
lean_inc_ref(v___x_1435_);
v___x_1436_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1434_, v___f_1431_, v_cache_1433_, v___x_1435_);
lean_dec_ref(v_cache_1433_);
v___x_1437_ = 1;
if (v___x_1436_ == 0)
{
lean_object* v___x_1438_; 
lean_inc(v_a_1429_);
lean_inc_ref(v_a_1428_);
lean_inc(v_a_1427_);
lean_inc_ref(v_a_1426_);
lean_inc(v_a_1425_);
lean_inc_ref(v_a_1424_);
lean_inc(v_a_1423_);
lean_inc(v_a_1422_);
lean_inc_ref(v_a_1421_);
v___x_1438_ = lean_apply_12(v_k_1420_, v_e_1418_, v_depth_1419_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, lean_box(0));
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; uint8_t v___x_1440_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
v___x_1440_ = lean_unbox(v_a_1439_);
lean_dec(v_a_1439_);
if (v___x_1440_ == 0)
{
lean_dec_ref_known(v___x_1435_, 2);
return v___x_1438_;
}
else
{
lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1461_; 
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v___x_1438_, 0);
lean_dec(v_unused_1462_);
v___x_1442_ = v___x_1438_;
v_isShared_1443_ = v_isSharedCheck_1461_;
goto v_resetjp_1441_;
}
else
{
lean_dec(v___x_1438_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1461_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; uint8_t v_mentionsSort_1445_; lean_object* v_cache_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1460_; 
v___x_1444_ = lean_st_ref_take(v_a_1422_);
v_mentionsSort_1445_ = lean_ctor_get_uint8(v___x_1444_, sizeof(void*)*1);
v_cache_1446_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1448_ = v___x_1444_;
v_isShared_1449_ = v_isSharedCheck_1460_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_cache_1446_);
lean_dec(v___x_1444_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1460_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1450_ = lean_box(0);
v___x_1451_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_1434_, v___f_1431_, v_cache_1446_, v___x_1435_, v___x_1450_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 0, v___x_1451_);
v___x_1453_ = v___x_1448_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1451_);
lean_ctor_set_uint8(v_reuseFailAlloc_1459_, sizeof(void*)*1, v_mentionsSort_1445_);
v___x_1453_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1454_ = lean_st_ref_put(v_a_1422_, v___x_1453_);
v___x_1455_ = lean_box(v___x_1437_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1455_);
v___x_1457_ = v___x_1442_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
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
}
}
else
{
lean_dec_ref_known(v___x_1435_, 2);
return v___x_1438_;
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_dec_ref_known(v___x_1435_, 2);
lean_dec_ref(v_k_1420_);
lean_dec(v_depth_1419_);
lean_dec_ref(v_e_1418_);
v___x_1463_ = lean_box(v___x_1437_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___boxed(lean_object* v_e_1465_, lean_object* v_depth_1466_, lean_object* v_k_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache(v_e_1465_, v_depth_1466_, v_k_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___redArg(lean_object* v_e_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
if (lean_obj_tag(v_e_1479_) == 1)
{
lean_object* v_fvarId_1484_; lean_object* v___x_1485_; 
v_fvarId_1484_ = lean_ctor_get(v_e_1479_, 0);
lean_inc(v_fvarId_1484_);
lean_dec_ref_known(v_e_1479_, 1);
v___x_1485_ = l_Lean_FVarId_getType___redArg(v_fvarId_1484_, v_a_1480_, v_a_1481_, v_a_1482_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1495_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1495_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1495_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1490_ = l_Lean_Expr_isProp(v_a_1486_);
lean_dec(v_a_1486_);
v___x_1491_ = lean_box(v___x_1490_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1491_);
v___x_1493_ = v___x_1488_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
v_a_1496_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1485_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1485_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
uint8_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec_ref(v_e_1479_);
v___x_1504_ = 0;
v___x_1505_ = lean_box(v___x_1504_);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___redArg___boxed(lean_object* v_e_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___redArg(v_e_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
lean_dec_ref(v_a_1508_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom(lean_object* v_e_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___redArg(v_e_1513_, v_a_1519_, v_a_1521_, v_a_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___boxed(lean_object* v_e_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom(v_e_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg(lean_object* v_e_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
if (lean_obj_tag(v_e_1539_) == 1)
{
lean_object* v_fvarId_1544_; lean_object* v___x_1545_; 
v_fvarId_1544_ = lean_ctor_get(v_e_1539_, 0);
lean_inc(v_fvarId_1544_);
lean_dec_ref_known(v_e_1539_, 1);
v___x_1545_ = l_Lean_FVarId_getType___redArg(v_fvarId_1544_, v_a_1540_, v_a_1541_, v_a_1542_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1556_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1556_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1556_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg___closed__0));
v___x_1551_ = l_Lean_Expr_isConstOf(v_a_1546_, v___x_1550_);
lean_dec(v_a_1546_);
v___x_1552_ = lean_box(v___x_1551_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1552_);
v___x_1554_ = v___x_1548_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
v_a_1557_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1545_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1545_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_dec_ref(v_e_1539_);
v___x_1565_ = 0;
v___x_1566_ = lean_box(v___x_1565_);
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg___boxed(lean_object* v_e_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg(v_e_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec_ref(v_a_1569_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom(lean_object* v_e_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg(v_e_1574_, v_a_1580_, v_a_1582_, v_a_1583_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___boxed(lean_object* v_e_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom(v_e_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec_ref(v_a_1587_);
return v_res_1597_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg(lean_object* v_a_1598_, lean_object* v_x_1599_){
_start:
{
if (lean_obj_tag(v_x_1599_) == 0)
{
uint8_t v___x_1600_; 
v___x_1600_ = 0;
return v___x_1600_;
}
else
{
lean_object* v_key_1601_; lean_object* v_tail_1602_; lean_object* v_fst_1603_; lean_object* v_snd_1604_; lean_object* v_fst_1605_; lean_object* v_snd_1606_; size_t v___x_1607_; size_t v___x_1608_; uint8_t v___x_1609_; 
v_key_1601_ = lean_ctor_get(v_x_1599_, 0);
v_tail_1602_ = lean_ctor_get(v_x_1599_, 2);
v_fst_1603_ = lean_ctor_get(v_key_1601_, 0);
v_snd_1604_ = lean_ctor_get(v_key_1601_, 1);
v_fst_1605_ = lean_ctor_get(v_a_1598_, 0);
v_snd_1606_ = lean_ctor_get(v_a_1598_, 1);
v___x_1607_ = lean_ptr_addr(v_fst_1603_);
v___x_1608_ = lean_ptr_addr(v_fst_1605_);
v___x_1609_ = lean_usize_dec_eq(v___x_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
v_x_1599_ = v_tail_1602_;
goto _start;
}
else
{
uint8_t v___x_1611_; 
v___x_1611_ = lean_nat_dec_eq(v_snd_1604_, v_snd_1606_);
if (v___x_1611_ == 0)
{
v_x_1599_ = v_tail_1602_;
goto _start;
}
else
{
return v___x_1611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg___boxed(lean_object* v_a_1613_, lean_object* v_x_1614_){
_start:
{
uint8_t v_res_1615_; lean_object* v_r_1616_; 
v_res_1615_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg(v_a_1613_, v_x_1614_);
lean_dec(v_x_1614_);
lean_dec_ref(v_a_1613_);
v_r_1616_ = lean_box(v_res_1615_);
return v_r_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
if (lean_obj_tag(v_x_1618_) == 0)
{
return v_x_1617_;
}
else
{
lean_object* v_key_1619_; lean_object* v_value_1620_; lean_object* v_tail_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1651_; 
v_key_1619_ = lean_ctor_get(v_x_1618_, 0);
v_value_1620_ = lean_ctor_get(v_x_1618_, 1);
v_tail_1621_ = lean_ctor_get(v_x_1618_, 2);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_x_1618_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1623_ = v_x_1618_;
v_isShared_1624_ = v_isSharedCheck_1651_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_tail_1621_);
lean_inc(v_value_1620_);
lean_inc(v_key_1619_);
lean_dec(v_x_1618_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1651_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v_fst_1625_; lean_object* v_snd_1626_; lean_object* v___x_1627_; size_t v___x_1628_; size_t v___x_1629_; size_t v___x_1630_; uint64_t v___x_1631_; uint64_t v___x_1632_; uint64_t v___x_1633_; uint64_t v___x_1634_; uint64_t v___x_1635_; uint64_t v_fold_1636_; uint64_t v___x_1637_; uint64_t v___x_1638_; uint64_t v___x_1639_; size_t v___x_1640_; size_t v___x_1641_; size_t v___x_1642_; size_t v___x_1643_; size_t v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v_fst_1625_ = lean_ctor_get(v_key_1619_, 0);
v_snd_1626_ = lean_ctor_get(v_key_1619_, 1);
v___x_1627_ = lean_array_get_size(v_x_1617_);
v___x_1628_ = lean_ptr_addr(v_fst_1625_);
v___x_1629_ = ((size_t)3ULL);
v___x_1630_ = lean_usize_shift_right(v___x_1628_, v___x_1629_);
v___x_1631_ = lean_usize_to_uint64(v___x_1630_);
v___x_1632_ = lean_uint64_of_nat(v_snd_1626_);
v___x_1633_ = lean_uint64_mix_hash(v___x_1631_, v___x_1632_);
v___x_1634_ = 32ULL;
v___x_1635_ = lean_uint64_shift_right(v___x_1633_, v___x_1634_);
v_fold_1636_ = lean_uint64_xor(v___x_1633_, v___x_1635_);
v___x_1637_ = 16ULL;
v___x_1638_ = lean_uint64_shift_right(v_fold_1636_, v___x_1637_);
v___x_1639_ = lean_uint64_xor(v_fold_1636_, v___x_1638_);
v___x_1640_ = lean_uint64_to_usize(v___x_1639_);
v___x_1641_ = lean_usize_of_nat(v___x_1627_);
v___x_1642_ = ((size_t)1ULL);
v___x_1643_ = lean_usize_sub(v___x_1641_, v___x_1642_);
v___x_1644_ = lean_usize_land(v___x_1640_, v___x_1643_);
v___x_1645_ = lean_array_uget_borrowed(v_x_1617_, v___x_1644_);
lean_inc(v___x_1645_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 2, v___x_1645_);
v___x_1647_ = v___x_1623_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_key_1619_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_value_1620_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_array_uset(v_x_1617_, v___x_1644_, v___x_1647_);
v_x_1617_ = v___x_1648_;
v_x_1618_ = v_tail_1621_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6___redArg(lean_object* v_i_1652_, lean_object* v_source_1653_, lean_object* v_target_1654_){
_start:
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = lean_array_get_size(v_source_1653_);
v___x_1656_ = lean_nat_dec_lt(v_i_1652_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_dec_ref(v_source_1653_);
lean_dec(v_i_1652_);
return v_target_1654_;
}
else
{
lean_object* v_es_1657_; lean_object* v___x_1658_; lean_object* v_source_1659_; lean_object* v_target_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_es_1657_ = lean_array_fget(v_source_1653_, v_i_1652_);
v___x_1658_ = lean_box(0);
v_source_1659_ = lean_array_fset(v_source_1653_, v_i_1652_, v___x_1658_);
v_target_1660_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6_spec__7___redArg(v_target_1654_, v_es_1657_);
v___x_1661_ = lean_unsigned_to_nat(1u);
v___x_1662_ = lean_nat_add(v_i_1652_, v___x_1661_);
lean_dec(v_i_1652_);
v_i_1652_ = v___x_1662_;
v_source_1653_ = v_source_1659_;
v_target_1654_ = v_target_1660_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4___redArg(lean_object* v_data_1664_){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v_nbuckets_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1665_ = lean_array_get_size(v_data_1664_);
v___x_1666_ = lean_unsigned_to_nat(2u);
v_nbuckets_1667_ = lean_nat_mul(v___x_1665_, v___x_1666_);
v___x_1668_ = lean_unsigned_to_nat(0u);
v___x_1669_ = lean_box(0);
v___x_1670_ = lean_mk_array(v_nbuckets_1667_, v___x_1669_);
v___x_1671_ = lean_array_propagate_mark(v_data_1664_, v___x_1670_);
v___x_1672_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6___redArg(v___x_1668_, v_data_1664_, v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2___redArg(lean_object* v_m_1673_, lean_object* v_a_1674_, lean_object* v_b_1675_){
_start:
{
lean_object* v_size_1676_; lean_object* v_buckets_1677_; lean_object* v_fst_1678_; lean_object* v_snd_1679_; lean_object* v___x_1680_; size_t v___x_1681_; size_t v___x_1682_; size_t v___x_1683_; uint64_t v___x_1684_; uint64_t v___x_1685_; uint64_t v___x_1686_; uint64_t v___x_1687_; uint64_t v___x_1688_; uint64_t v_fold_1689_; uint64_t v___x_1690_; uint64_t v___x_1691_; uint64_t v___x_1692_; size_t v___x_1693_; size_t v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; lean_object* v_bkt_1698_; uint8_t v___x_1699_; 
v_size_1676_ = lean_ctor_get(v_m_1673_, 0);
v_buckets_1677_ = lean_ctor_get(v_m_1673_, 1);
v_fst_1678_ = lean_ctor_get(v_a_1674_, 0);
v_snd_1679_ = lean_ctor_get(v_a_1674_, 1);
v___x_1680_ = lean_array_get_size(v_buckets_1677_);
v___x_1681_ = lean_ptr_addr(v_fst_1678_);
v___x_1682_ = ((size_t)3ULL);
v___x_1683_ = lean_usize_shift_right(v___x_1681_, v___x_1682_);
v___x_1684_ = lean_usize_to_uint64(v___x_1683_);
v___x_1685_ = lean_uint64_of_nat(v_snd_1679_);
v___x_1686_ = lean_uint64_mix_hash(v___x_1684_, v___x_1685_);
v___x_1687_ = 32ULL;
v___x_1688_ = lean_uint64_shift_right(v___x_1686_, v___x_1687_);
v_fold_1689_ = lean_uint64_xor(v___x_1686_, v___x_1688_);
v___x_1690_ = 16ULL;
v___x_1691_ = lean_uint64_shift_right(v_fold_1689_, v___x_1690_);
v___x_1692_ = lean_uint64_xor(v_fold_1689_, v___x_1691_);
v___x_1693_ = lean_uint64_to_usize(v___x_1692_);
v___x_1694_ = lean_usize_of_nat(v___x_1680_);
v___x_1695_ = ((size_t)1ULL);
v___x_1696_ = lean_usize_sub(v___x_1694_, v___x_1695_);
v___x_1697_ = lean_usize_land(v___x_1693_, v___x_1696_);
v_bkt_1698_ = lean_array_uget_borrowed(v_buckets_1677_, v___x_1697_);
v___x_1699_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg(v_a_1674_, v_bkt_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1720_; 
lean_inc_ref(v_buckets_1677_);
lean_inc(v_size_1676_);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_m_1673_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; lean_object* v_unused_1722_; 
v_unused_1721_ = lean_ctor_get(v_m_1673_, 1);
lean_dec(v_unused_1721_);
v_unused_1722_ = lean_ctor_get(v_m_1673_, 0);
lean_dec(v_unused_1722_);
v___x_1701_ = v_m_1673_;
v_isShared_1702_ = v_isSharedCheck_1720_;
goto v_resetjp_1700_;
}
else
{
lean_dec(v_m_1673_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1720_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v_size_x27_1704_; lean_object* v___x_1705_; lean_object* v_buckets_x27_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1703_ = lean_unsigned_to_nat(1u);
v_size_x27_1704_ = lean_nat_add(v_size_1676_, v___x_1703_);
lean_dec(v_size_1676_);
lean_inc(v_bkt_1698_);
v___x_1705_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1705_, 0, v_a_1674_);
lean_ctor_set(v___x_1705_, 1, v_b_1675_);
lean_ctor_set(v___x_1705_, 2, v_bkt_1698_);
v_buckets_x27_1706_ = lean_array_uset(v_buckets_1677_, v___x_1697_, v___x_1705_);
v___x_1707_ = lean_unsigned_to_nat(4u);
v___x_1708_ = lean_nat_mul(v_size_x27_1704_, v___x_1707_);
v___x_1709_ = lean_unsigned_to_nat(3u);
v___x_1710_ = lean_nat_div(v___x_1708_, v___x_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_array_get_size(v_buckets_x27_1706_);
v___x_1712_ = lean_nat_dec_le(v___x_1710_, v___x_1711_);
lean_dec(v___x_1710_);
if (v___x_1712_ == 0)
{
lean_object* v_val_1713_; lean_object* v___x_1715_; 
v_val_1713_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4___redArg(v_buckets_x27_1706_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v_val_1713_);
lean_ctor_set(v___x_1701_, 0, v_size_x27_1704_);
v___x_1715_ = v___x_1701_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_size_x27_1704_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_val_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
else
{
lean_object* v___x_1718_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v_buckets_x27_1706_);
lean_ctor_set(v___x_1701_, 0, v_size_x27_1704_);
v___x_1718_ = v___x_1701_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_size_x27_1704_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_buckets_x27_1706_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_dec(v_b_1675_);
lean_dec_ref(v_a_1674_);
return v_m_1673_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg(lean_object* v_m_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_buckets_1725_; lean_object* v_fst_1726_; lean_object* v_snd_1727_; lean_object* v___x_1728_; size_t v___x_1729_; size_t v___x_1730_; size_t v___x_1731_; uint64_t v___x_1732_; uint64_t v___x_1733_; uint64_t v___x_1734_; uint64_t v___x_1735_; uint64_t v___x_1736_; uint64_t v_fold_1737_; uint64_t v___x_1738_; uint64_t v___x_1739_; uint64_t v___x_1740_; size_t v___x_1741_; size_t v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; size_t v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v_buckets_1725_ = lean_ctor_get(v_m_1723_, 1);
v_fst_1726_ = lean_ctor_get(v_a_1724_, 0);
v_snd_1727_ = lean_ctor_get(v_a_1724_, 1);
v___x_1728_ = lean_array_get_size(v_buckets_1725_);
v___x_1729_ = lean_ptr_addr(v_fst_1726_);
v___x_1730_ = ((size_t)3ULL);
v___x_1731_ = lean_usize_shift_right(v___x_1729_, v___x_1730_);
v___x_1732_ = lean_usize_to_uint64(v___x_1731_);
v___x_1733_ = lean_uint64_of_nat(v_snd_1727_);
v___x_1734_ = lean_uint64_mix_hash(v___x_1732_, v___x_1733_);
v___x_1735_ = 32ULL;
v___x_1736_ = lean_uint64_shift_right(v___x_1734_, v___x_1735_);
v_fold_1737_ = lean_uint64_xor(v___x_1734_, v___x_1736_);
v___x_1738_ = 16ULL;
v___x_1739_ = lean_uint64_shift_right(v_fold_1737_, v___x_1738_);
v___x_1740_ = lean_uint64_xor(v_fold_1737_, v___x_1739_);
v___x_1741_ = lean_uint64_to_usize(v___x_1740_);
v___x_1742_ = lean_usize_of_nat(v___x_1728_);
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_sub(v___x_1742_, v___x_1743_);
v___x_1745_ = lean_usize_land(v___x_1741_, v___x_1744_);
v___x_1746_ = lean_array_uget_borrowed(v_buckets_1725_, v___x_1745_);
v___x_1747_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg(v_a_1724_, v___x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg___boxed(lean_object* v_m_1748_, lean_object* v_a_1749_){
_start:
{
uint8_t v_res_1750_; lean_object* v_r_1751_; 
v_res_1750_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg(v_m_1748_, v_a_1749_);
lean_dec_ref(v_a_1749_);
lean_dec_ref(v_m_1748_);
v_r_1751_ = lean_box(v_res_1750_);
return v_r_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go(lean_object* v_e_1813_, lean_object* v_depth_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v_p_1844_; lean_object* v_q_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; 
if (lean_obj_tag(v_e_1813_) == 7)
{
lean_object* v_binderType_1859_; lean_object* v_body_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v_binderType_1859_ = lean_ctor_get(v_e_1813_, 1);
lean_inc_ref(v_binderType_1859_);
v_body_1860_ = lean_ctor_get(v_e_1813_, 2);
lean_inc_ref(v_body_1860_);
lean_dec_ref_known(v_e_1813_, 3);
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = lean_expr_has_loose_bvar(v_body_1860_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; 
lean_inc(v_depth_1814_);
v___x_1863_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_binderType_1859_, v_depth_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; uint8_t v___x_1865_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v___x_1865_ = lean_unbox(v_a_1864_);
if (v___x_1865_ == 0)
{
lean_dec_ref(v_body_1860_);
lean_dec(v_depth_1814_);
return v___x_1863_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_dec_ref_known(v___x_1863_, 1);
v___x_1866_ = lean_unsigned_to_nat(1u);
v___x_1867_ = lean_nat_add(v_depth_1814_, v___x_1866_);
lean_dec(v_depth_1814_);
v___x_1868_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_body_1860_, v___x_1867_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
return v___x_1868_;
}
}
else
{
lean_dec_ref(v_body_1860_);
lean_dec(v_depth_1814_);
return v___x_1863_;
}
}
else
{
uint8_t v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_dec_ref(v_body_1860_);
lean_dec_ref(v_binderType_1859_);
lean_dec(v_depth_1814_);
v___x_1869_ = 0;
v___x_1870_ = lean_box(v___x_1869_);
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
}
else
{
lean_object* v___x_1872_; 
lean_inc_ref(v_e_1813_);
v___x_1872_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1813_, v_a_1821_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1874_ = l_Lean_Expr_cleanupAnnotations(v_a_1873_);
lean_dec(v_a_1873_);
v___x_1875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__1));
v___x_1876_ = l_Lean_Expr_isConstOf(v___x_1874_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__3));
v___x_1878_ = l_Lean_Expr_isConstOf(v___x_1874_, v___x_1877_);
if (v___x_1878_ == 0)
{
uint8_t v___x_1879_; 
v___x_1879_ = l_Lean_Expr_isApp(v___x_1874_);
if (v___x_1879_ == 0)
{
lean_dec_ref(v___x_1874_);
v___y_1830_ = v_a_1815_;
v___y_1831_ = v_a_1816_;
v___y_1832_ = v_a_1817_;
v___y_1833_ = v_a_1818_;
v___y_1834_ = v_a_1819_;
v___y_1835_ = v_a_1820_;
v___y_1836_ = v_a_1821_;
v___y_1837_ = v_a_1822_;
v___y_1838_ = v_a_1823_;
goto v___jp_1829_;
}
else
{
lean_object* v_arg_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v_arg_1880_ = lean_ctor_get(v___x_1874_, 1);
lean_inc_ref(v_arg_1880_);
v___x_1881_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1874_);
lean_dec_ref(v___x_1874_);
v___x_1882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__5));
v___x_1883_ = l_Lean_Expr_isConstOf(v___x_1881_, v___x_1882_);
if (v___x_1883_ == 0)
{
uint8_t v___x_1884_; 
v___x_1884_ = l_Lean_Expr_isApp(v___x_1881_);
if (v___x_1884_ == 0)
{
lean_dec_ref(v___x_1881_);
lean_dec_ref(v_arg_1880_);
v___y_1830_ = v_a_1815_;
v___y_1831_ = v_a_1816_;
v___y_1832_ = v_a_1817_;
v___y_1833_ = v_a_1818_;
v___y_1834_ = v_a_1819_;
v___y_1835_ = v_a_1820_;
v___y_1836_ = v_a_1821_;
v___y_1837_ = v_a_1822_;
v___y_1838_ = v_a_1823_;
goto v___jp_1829_;
}
else
{
lean_object* v_arg_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v_arg_1885_ = lean_ctor_get(v___x_1881_, 1);
lean_inc_ref(v_arg_1885_);
v___x_1886_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1881_);
lean_dec_ref(v___x_1881_);
v___x_1887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__7));
v___x_1888_ = l_Lean_Expr_isConstOf(v___x_1886_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__9));
v___x_1890_ = l_Lean_Expr_isConstOf(v___x_1886_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__11));
v___x_1892_ = l_Lean_Expr_isConstOf(v___x_1886_, v___x_1891_);
if (v___x_1892_ == 0)
{
uint8_t v___x_1893_; 
v___x_1893_ = l_Lean_Expr_isApp(v___x_1886_);
if (v___x_1893_ == 0)
{
lean_dec_ref(v___x_1886_);
lean_dec_ref(v_arg_1885_);
lean_dec_ref(v_arg_1880_);
v___y_1830_ = v_a_1815_;
v___y_1831_ = v_a_1816_;
v___y_1832_ = v_a_1817_;
v___y_1833_ = v_a_1818_;
v___y_1834_ = v_a_1819_;
v___y_1835_ = v_a_1820_;
v___y_1836_ = v_a_1821_;
v___y_1837_ = v_a_1822_;
v___y_1838_ = v_a_1823_;
goto v___jp_1829_;
}
else
{
lean_object* v_arg_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v_arg_1894_ = lean_ctor_get(v___x_1886_, 1);
lean_inc_ref(v_arg_1894_);
v___x_1895_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1886_);
lean_dec_ref(v___x_1886_);
v___x_1896_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__13));
v___x_1897_ = l_Lean_Expr_isConstOf(v___x_1895_, v___x_1896_);
if (v___x_1897_ == 0)
{
uint8_t v___x_1898_; 
v___x_1898_ = l_Lean_Expr_isApp(v___x_1895_);
if (v___x_1898_ == 0)
{
lean_dec_ref(v___x_1895_);
lean_dec_ref(v_arg_1894_);
lean_dec_ref(v_arg_1885_);
lean_dec_ref(v_arg_1880_);
v___y_1830_ = v_a_1815_;
v___y_1831_ = v_a_1816_;
v___y_1832_ = v_a_1817_;
v___y_1833_ = v_a_1818_;
v___y_1834_ = v_a_1819_;
v___y_1835_ = v_a_1820_;
v___y_1836_ = v_a_1821_;
v___y_1837_ = v_a_1822_;
v___y_1838_ = v_a_1823_;
goto v___jp_1829_;
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1899_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1895_);
v___x_1900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__16));
v___x_1901_ = l_Lean_Expr_isConstOf(v___x_1899_, v___x_1900_);
if (v___x_1901_ == 0)
{
uint8_t v___x_1902_; 
lean_dec_ref(v_arg_1894_);
v___x_1902_ = l_Lean_Expr_isApp(v___x_1899_);
if (v___x_1902_ == 0)
{
lean_dec_ref(v___x_1899_);
lean_dec_ref(v___x_1895_);
lean_dec_ref(v_arg_1885_);
lean_dec_ref(v_arg_1880_);
v___y_1830_ = v_a_1815_;
v___y_1831_ = v_a_1816_;
v___y_1832_ = v_a_1817_;
v___y_1833_ = v_a_1818_;
v___y_1834_ = v_a_1819_;
v___y_1835_ = v_a_1820_;
v___y_1836_ = v_a_1821_;
v___y_1837_ = v_a_1822_;
v___y_1838_ = v_a_1823_;
goto v___jp_1829_;
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1903_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1899_);
lean_dec_ref(v___x_1899_);
v___x_1904_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__21));
v___x_1905_ = l_Lean_Expr_isConstOf(v___x_1903_, v___x_1904_);
lean_dec_ref(v___x_1903_);
if (v___x_1905_ == 0)
{
lean_dec_ref(v___x_1895_);
lean_dec_ref(v_arg_1885_);
lean_dec_ref(v_arg_1880_);
v___y_1830_ = v_a_1815_;
v___y_1831_ = v_a_1816_;
v___y_1832_ = v_a_1817_;
v___y_1833_ = v_a_1818_;
v___y_1834_ = v_a_1819_;
v___y_1835_ = v_a_1820_;
v___y_1836_ = v_a_1821_;
v___y_1837_ = v_a_1822_;
v___y_1838_ = v_a_1823_;
goto v___jp_1829_;
}
else
{
lean_object* v_arg_1906_; lean_object* v___x_1907_; 
lean_dec_ref(v_e_1813_);
v_arg_1906_ = lean_ctor_get(v___x_1895_, 1);
lean_inc_ref(v_arg_1906_);
lean_dec_ref(v___x_1895_);
lean_inc(v_depth_1814_);
v___x_1907_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1906_, v_depth_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; uint8_t v___x_1909_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v___x_1909_ = lean_unbox(v_a_1908_);
if (v___x_1909_ == 0)
{
lean_dec_ref(v_arg_1885_);
lean_dec_ref(v_arg_1880_);
lean_dec(v_depth_1814_);
return v___x_1907_;
}
else
{
lean_object* v___x_1910_; 
lean_dec_ref_known(v___x_1907_, 1);
lean_inc(v_depth_1814_);
v___x_1910_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1885_, v_depth_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; uint8_t v___x_1912_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v___x_1912_ = lean_unbox(v_a_1911_);
if (v___x_1912_ == 0)
{
lean_dec_ref(v_arg_1880_);
lean_dec(v_depth_1814_);
return v___x_1910_;
}
else
{
lean_object* v___x_1913_; 
lean_dec_ref_known(v___x_1910_, 1);
v___x_1913_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1880_, v_depth_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
return v___x_1913_;
}
}
else
{
lean_dec_ref(v_arg_1880_);
lean_dec(v_depth_1814_);
return v___x_1910_;
}
}
}
else
{
lean_dec_ref(v_arg_1885_);
lean_dec_ref(v_arg_1880_);
lean_dec(v_depth_1814_);
return v___x_1907_;
}
}
}
}
else
{
lean_object* v___x_1914_; 
lean_dec_ref(v___x_1899_);
lean_dec_ref(v___x_1895_);
lean_dec_ref(v_e_1813_);
lean_inc(v_depth_1814_);
v___x_1914_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_1894_, v_depth_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; uint8_t v___x_1916_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v___x_1916_ = lean_unbox(v_a_1915_);
if (v___x_1916_ == 0)
{
lean_dec_ref(v_arg_1885_);
lean_dec_ref(v_arg_1880_);
lean_dec(v_depth_1814_);
return v___x_1914_;
}
else
{
lean_object* v___x_1917_; 
lean_dec_ref_known(v___x_1914_, 1);
lean_inc(v_depth_1814_);
v___x_1917_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1885_, v_depth_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; uint8_t v___x_1919_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v___x_1919_ = lean_unbox(v_a_1918_);
if (v___x_1919_ == 0)
{
lean_dec_ref(v_arg_1880_);
lean_dec(v_depth_1814_);
return v___x_1917_;
}
else
{
lean_object* v___x_1920_; 
lean_dec_ref_known(v___x_1917_, 1);
v___x_1920_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1880_, v_depth_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
return v___x_1920_;
}
}
else
{
lean_dec_ref(v_arg_1880_);
lean_dec(v_depth_1814_);
return v___x_1917_;
}
}
}
else
{
lean_dec_ref(v_arg_1885_);
lean_dec_ref(v_arg_1880_);
lean_dec(v_depth_1814_);
return v___x_1914_;
}
}
}
}
else
{
uint8_t v___x_1921_; 
lean_dec_ref(v___x_1895_);
lean_dec_ref(v_e_1813_);
v___x_1921_ = l_Lean_Expr_isProp(v_arg_1894_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg___closed__0));
v___x_1923_ = l_Lean_Expr_isConstOf(v_arg_1894_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; 
v___x_1924_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___redArg(v_arg_1894_, v_arg_1885_, v_arg_1880_, v_depth_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_depth_1814_);
lean_dec_ref(v_arg_1880_);
lean_dec_ref(v_arg_1885_);
lean_dec_ref(v_arg_1894_);
return v___x_1924_;
}
else
{
lean_object* v___x_1925_; 
lean_dec_ref(v_arg_1894_);
lean_inc(v_depth_1814_);
v___x_1925_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_1885_, v_depth_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; uint8_t v___x_1927_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v___x_1927_ = lean_unbox(v_a_1926_);
if (v___x_1927_ == 0)
{
lean_dec_ref(v_arg_1880_);
lean_dec(v_depth_1814_);
return v___x_1925_;
}
else
{
lean_object* v___x_1928_; 
lean_dec_ref_known(v___x_1925_, 1);
v___x_1928_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_1880_, v_depth_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
return v___x_1928_;
}
}
else
{
lean_dec_ref(v_arg_1880_);
lean_dec(v_depth_1814_);
return v___x_1925_;
}
}
}
else
{
lean_object* v___x_1929_; 
lean_dec_ref(v_arg_1894_);
lean_inc(v_depth_1814_);
v___x_1929_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1885_, v_depth_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; uint8_t v___x_1931_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v___x_1931_ = lean_unbox(v_a_1930_);
if (v___x_1931_ == 0)
{
lean_dec_ref(v_arg_1880_);
lean_dec(v_depth_1814_);
return v___x_1929_;
}
else
{
lean_object* v___x_1932_; 
lean_dec_ref_known(v___x_1929_, 1);
v___x_1932_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1880_, v_depth_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
return v___x_1932_;
}
}
else
{
lean_dec_ref(v_arg_1880_);
lean_dec(v_depth_1814_);
return v___x_1929_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1886_);
lean_dec_ref(v_e_1813_);
v_p_1844_ = v_arg_1885_;
v_q_1845_ = v_arg_1880_;
v___y_1846_ = v_a_1815_;
v___y_1847_ = v_a_1816_;
v___y_1848_ = v_a_1817_;
v___y_1849_ = v_a_1818_;
v___y_1850_ = v_a_1819_;
v___y_1851_ = v_a_1820_;
v___y_1852_ = v_a_1821_;
v___y_1853_ = v_a_1822_;
v___y_1854_ = v_a_1823_;
goto v___jp_1843_;
}
}
else
{
lean_dec_ref(v___x_1886_);
lean_dec_ref(v_e_1813_);
v_p_1844_ = v_arg_1885_;
v_q_1845_ = v_arg_1880_;
v___y_1846_ = v_a_1815_;
v___y_1847_ = v_a_1816_;
v___y_1848_ = v_a_1817_;
v___y_1849_ = v_a_1818_;
v___y_1850_ = v_a_1819_;
v___y_1851_ = v_a_1820_;
v___y_1852_ = v_a_1821_;
v___y_1853_ = v_a_1822_;
v___y_1854_ = v_a_1823_;
goto v___jp_1843_;
}
}
else
{
lean_dec_ref(v___x_1886_);
lean_dec_ref(v_e_1813_);
v_p_1844_ = v_arg_1885_;
v_q_1845_ = v_arg_1880_;
v___y_1846_ = v_a_1815_;
v___y_1847_ = v_a_1816_;
v___y_1848_ = v_a_1817_;
v___y_1849_ = v_a_1818_;
v___y_1850_ = v_a_1819_;
v___y_1851_ = v_a_1820_;
v___y_1852_ = v_a_1821_;
v___y_1853_ = v_a_1822_;
v___y_1854_ = v_a_1823_;
goto v___jp_1843_;
}
}
}
else
{
lean_object* v___x_1933_; 
lean_dec_ref(v___x_1881_);
lean_dec_ref(v_e_1813_);
v___x_1933_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1880_, v_depth_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
return v___x_1933_;
}
}
}
else
{
lean_dec_ref(v___x_1874_);
lean_dec(v_depth_1814_);
lean_dec_ref(v_e_1813_);
goto v___jp_1825_;
}
}
else
{
lean_dec_ref(v___x_1874_);
lean_dec(v_depth_1814_);
lean_dec_ref(v_e_1813_);
goto v___jp_1825_;
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec(v_depth_1814_);
lean_dec_ref(v_e_1813_);
v_a_1934_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1872_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1872_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
v___jp_1825_:
{
uint8_t v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = 1;
v___x_1827_ = lean_box(v___x_1826_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
v___jp_1829_:
{
lean_object* v___x_1839_; 
lean_inc_ref(v_e_1813_);
v___x_1839_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp(v_e_1813_, v_depth_1814_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v_depth_1814_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; uint8_t v___x_1841_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v___x_1841_ = lean_unbox(v_a_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
lean_dec_ref_known(v___x_1839_, 1);
v___x_1842_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___redArg(v_e_1813_, v___y_1835_, v___y_1837_, v___y_1838_);
return v___x_1842_;
}
else
{
lean_dec_ref(v_e_1813_);
return v___x_1839_;
}
}
else
{
lean_dec_ref(v_e_1813_);
return v___x_1839_;
}
}
v___jp_1843_:
{
lean_object* v___x_1855_; 
lean_inc(v_depth_1814_);
v___x_1855_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_p_1844_, v_depth_1814_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; uint8_t v___x_1857_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v___x_1857_ = lean_unbox(v_a_1856_);
if (v___x_1857_ == 0)
{
lean_dec_ref(v_q_1845_);
lean_dec(v_depth_1814_);
return v___x_1855_;
}
else
{
lean_object* v___x_1858_; 
lean_dec_ref_known(v___x_1855_, 1);
v___x_1858_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_q_1845_, v_depth_1814_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
return v___x_1858_;
}
}
else
{
lean_dec_ref(v_q_1845_);
lean_dec(v_depth_1814_);
return v___x_1855_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(lean_object* v_e_1942_, lean_object* v_depth_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v___x_1954_; lean_object* v_cache_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; uint8_t v___x_1958_; 
v___x_1954_ = lean_st_ref_get(v_a_1945_);
v_cache_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc_ref(v_cache_1955_);
lean_dec(v___x_1954_);
lean_inc(v_depth_1943_);
lean_inc_ref(v_e_1942_);
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v_e_1942_);
lean_ctor_set(v___x_1956_, 1, v_depth_1943_);
v___x_1957_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg(v_cache_1955_, v___x_1956_);
lean_dec_ref(v_cache_1955_);
v___x_1958_ = 1;
if (v___x_1957_ == 0)
{
lean_object* v___x_1959_; 
v___x_1959_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go(v_e_1942_, v_depth_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; uint8_t v___x_1961_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
v___x_1961_ = lean_unbox(v_a_1960_);
if (v___x_1961_ == 0)
{
lean_dec_ref_known(v___x_1956_, 2);
return v___x_1959_;
}
else
{
lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1982_; 
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v___x_1959_, 0);
lean_dec(v_unused_1983_);
v___x_1963_ = v___x_1959_;
v_isShared_1964_ = v_isSharedCheck_1982_;
goto v_resetjp_1962_;
}
else
{
lean_dec(v___x_1959_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1982_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; uint8_t v_mentionsSort_1966_; lean_object* v_cache_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1981_; 
v___x_1965_ = lean_st_ref_take(v_a_1945_);
v_mentionsSort_1966_ = lean_ctor_get_uint8(v___x_1965_, sizeof(void*)*1);
v_cache_1967_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1969_ = v___x_1965_;
v_isShared_1970_ = v_isSharedCheck_1981_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_cache_1967_);
lean_dec(v___x_1965_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1981_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1971_ = lean_box(0);
v___x_1972_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2___redArg(v_cache_1967_, v___x_1956_, v___x_1971_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1972_);
v___x_1974_ = v___x_1969_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1980_, sizeof(void*)*1, v_mentionsSort_1966_);
v___x_1974_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1975_ = lean_st_ref_put(v_a_1945_, v___x_1974_);
v___x_1976_ = lean_box(v___x_1958_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1976_);
v___x_1978_ = v___x_1963_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
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
}
}
else
{
lean_dec_ref_known(v___x_1956_, 2);
return v___x_1959_;
}
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec_ref_known(v___x_1956_, 2);
lean_dec(v_depth_1943_);
lean_dec_ref(v_e_1942_);
v___x_1984_ = lean_box(v___x_1958_);
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
return v___x_1985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go(lean_object* v_e_1986_, lean_object* v_depth_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v_p_2017_; lean_object* v_q_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___x_2032_; 
lean_inc_ref(v_e_1986_);
v___x_2032_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1986_, v_a_1994_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2098_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2035_ = v___x_2032_;
v_isShared_2036_ = v_isSharedCheck_2098_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2032_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2098_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2037_ = l_Lean_Expr_cleanupAnnotations(v_a_2033_);
lean_dec(v_a_2033_);
v___x_2038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__1));
v___x_2039_ = l_Lean_Expr_isConstOf(v___x_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2040_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__3));
v___x_2041_ = l_Lean_Expr_isConstOf(v___x_2037_, v___x_2040_);
if (v___x_2041_ == 0)
{
uint8_t v___x_2042_; 
v___x_2042_ = l_Lean_Expr_isApp(v___x_2037_);
if (v___x_2042_ == 0)
{
lean_dec_ref(v___x_2037_);
lean_del_object(v___x_2035_);
v___y_2003_ = v_a_1988_;
v___y_2004_ = v_a_1989_;
v___y_2005_ = v_a_1990_;
v___y_2006_ = v_a_1991_;
v___y_2007_ = v_a_1992_;
v___y_2008_ = v_a_1993_;
v___y_2009_ = v_a_1994_;
v___y_2010_ = v_a_1995_;
v___y_2011_ = v_a_1996_;
goto v___jp_2002_;
}
else
{
lean_object* v_arg_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v_arg_2043_ = lean_ctor_get(v___x_2037_, 1);
lean_inc_ref(v_arg_2043_);
v___x_2044_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2037_);
lean_dec_ref(v___x_2037_);
v___x_2045_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__5));
v___x_2046_ = l_Lean_Expr_isConstOf(v___x_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
uint8_t v___x_2047_; 
v___x_2047_ = l_Lean_Expr_isApp(v___x_2044_);
if (v___x_2047_ == 0)
{
lean_dec_ref(v___x_2044_);
lean_dec_ref(v_arg_2043_);
lean_del_object(v___x_2035_);
v___y_2003_ = v_a_1988_;
v___y_2004_ = v_a_1989_;
v___y_2005_ = v_a_1990_;
v___y_2006_ = v_a_1991_;
v___y_2007_ = v_a_1992_;
v___y_2008_ = v_a_1993_;
v___y_2009_ = v_a_1994_;
v___y_2010_ = v_a_1995_;
v___y_2011_ = v_a_1996_;
goto v___jp_2002_;
}
else
{
lean_object* v_arg_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v_arg_2048_ = lean_ctor_get(v___x_2044_, 1);
lean_inc_ref(v_arg_2048_);
v___x_2049_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2044_);
lean_dec_ref(v___x_2044_);
v___x_2050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__8));
v___x_2051_ = l_Lean_Expr_isConstOf(v___x_2049_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__10));
v___x_2053_ = l_Lean_Expr_isConstOf(v___x_2049_, v___x_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2054_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__12));
v___x_2055_ = l_Lean_Expr_isConstOf(v___x_2049_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__14));
v___x_2057_ = l_Lean_Expr_isConstOf(v___x_2049_, v___x_2056_);
if (v___x_2057_ == 0)
{
uint8_t v___x_2058_; 
v___x_2058_ = l_Lean_Expr_isApp(v___x_2049_);
if (v___x_2058_ == 0)
{
lean_dec_ref(v___x_2049_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_arg_2043_);
lean_del_object(v___x_2035_);
v___y_2003_ = v_a_1988_;
v___y_2004_ = v_a_1989_;
v___y_2005_ = v_a_1990_;
v___y_2006_ = v_a_1991_;
v___y_2007_ = v_a_1992_;
v___y_2008_ = v_a_1993_;
v___y_2009_ = v_a_1994_;
v___y_2010_ = v_a_1995_;
v___y_2011_ = v_a_1996_;
goto v___jp_2002_;
}
else
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2049_);
v___x_2060_ = l_Lean_Expr_isApp(v___x_2059_);
if (v___x_2060_ == 0)
{
lean_dec_ref(v___x_2059_);
lean_dec_ref(v___x_2049_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_arg_2043_);
lean_del_object(v___x_2035_);
v___y_2003_ = v_a_1988_;
v___y_2004_ = v_a_1989_;
v___y_2005_ = v_a_1990_;
v___y_2006_ = v_a_1991_;
v___y_2007_ = v_a_1992_;
v___y_2008_ = v_a_1993_;
v___y_2009_ = v_a_1994_;
v___y_2010_ = v_a_1995_;
v___y_2011_ = v_a_1996_;
goto v___jp_2002_;
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2061_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2059_);
v___x_2062_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__16));
v___x_2063_ = l_Lean_Expr_isConstOf(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v_arg_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
lean_dec_ref(v___x_2049_);
v_arg_2064_ = lean_ctor_get(v___x_2059_, 1);
lean_inc_ref(v_arg_2064_);
lean_dec_ref(v___x_2059_);
v___x_2065_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__19));
v___x_2066_ = l_Lean_Expr_isConstOf(v___x_2061_, v___x_2065_);
if (v___x_2066_ == 0)
{
uint8_t v___x_2067_; 
lean_del_object(v___x_2035_);
v___x_2067_ = l_Lean_Expr_isApp(v___x_2061_);
if (v___x_2067_ == 0)
{
lean_dec_ref(v_arg_2064_);
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_arg_2043_);
v___y_2003_ = v_a_1988_;
v___y_2004_ = v_a_1989_;
v___y_2005_ = v_a_1990_;
v___y_2006_ = v_a_1991_;
v___y_2007_ = v_a_1992_;
v___y_2008_ = v_a_1993_;
v___y_2009_ = v_a_1994_;
v___y_2010_ = v_a_1995_;
v___y_2011_ = v_a_1996_;
goto v___jp_2002_;
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2068_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2061_);
lean_dec_ref(v___x_2061_);
v___x_2069_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__21));
v___x_2070_ = l_Lean_Expr_isConstOf(v___x_2068_, v___x_2069_);
lean_dec_ref(v___x_2068_);
if (v___x_2070_ == 0)
{
lean_dec_ref(v_arg_2064_);
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_arg_2043_);
v___y_2003_ = v_a_1988_;
v___y_2004_ = v_a_1989_;
v___y_2005_ = v_a_1990_;
v___y_2006_ = v_a_1991_;
v___y_2007_ = v_a_1992_;
v___y_2008_ = v_a_1993_;
v___y_2009_ = v_a_1994_;
v___y_2010_ = v_a_1995_;
v___y_2011_ = v_a_1996_;
goto v___jp_2002_;
}
else
{
lean_object* v___x_2071_; 
lean_dec_ref(v_e_1986_);
lean_inc(v_depth_1987_);
v___x_2071_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_2064_, v_depth_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; uint8_t v___x_2073_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v___x_2073_ = lean_unbox(v_a_2072_);
if (v___x_2073_ == 0)
{
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_arg_2043_);
lean_dec(v_depth_1987_);
return v___x_2071_;
}
else
{
lean_object* v___x_2074_; 
lean_dec_ref_known(v___x_2071_, 1);
lean_inc(v_depth_1987_);
v___x_2074_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2048_, v_depth_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; uint8_t v___x_2076_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v___x_2076_ = lean_unbox(v_a_2075_);
if (v___x_2076_ == 0)
{
lean_dec_ref(v_arg_2043_);
lean_dec(v_depth_1987_);
return v___x_2074_;
}
else
{
lean_object* v___x_2077_; 
lean_dec_ref_known(v___x_2074_, 1);
v___x_2077_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2043_, v_depth_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
return v___x_2077_;
}
}
else
{
lean_dec_ref(v_arg_2043_);
lean_dec(v_depth_1987_);
return v___x_2074_;
}
}
}
else
{
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_arg_2043_);
lean_dec(v_depth_1987_);
return v___x_2071_;
}
}
}
}
else
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
lean_dec_ref(v___x_2061_);
lean_dec_ref(v_e_1986_);
v___x_2078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg___closed__0));
v___x_2079_ = l_Lean_Expr_isConstOf(v_arg_2064_, v___x_2078_);
lean_dec_ref(v_arg_2064_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_arg_2043_);
lean_dec(v_depth_1987_);
v___x_2080_ = lean_box(v___x_2079_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2080_);
v___x_2082_ = v___x_2035_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
else
{
lean_object* v___x_2084_; 
lean_del_object(v___x_2035_);
lean_inc(v_depth_1987_);
v___x_2084_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2048_, v_depth_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; uint8_t v___x_2086_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v___x_2086_ = lean_unbox(v_a_2085_);
if (v___x_2086_ == 0)
{
lean_dec_ref(v_arg_2043_);
lean_dec(v_depth_1987_);
return v___x_2084_;
}
else
{
lean_object* v___x_2087_; 
lean_dec_ref_known(v___x_2084_, 1);
v___x_2087_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2043_, v_depth_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
return v___x_2087_;
}
}
else
{
lean_dec_ref(v_arg_2043_);
lean_dec(v_depth_1987_);
return v___x_2084_;
}
}
}
}
else
{
lean_object* v_arg_2088_; lean_object* v___x_2089_; 
lean_dec_ref(v___x_2061_);
lean_dec_ref(v___x_2059_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_e_1986_);
v_arg_2088_ = lean_ctor_get(v___x_2049_, 1);
lean_inc_ref(v_arg_2088_);
lean_dec_ref(v___x_2049_);
lean_inc(v_depth_1987_);
v___x_2089_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2088_, v_depth_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; uint8_t v___x_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v___x_2091_ = lean_unbox(v_a_2090_);
if (v___x_2091_ == 0)
{
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_arg_2043_);
lean_dec(v_depth_1987_);
return v___x_2089_;
}
else
{
lean_object* v___x_2092_; 
lean_dec_ref_known(v___x_2089_, 1);
lean_inc(v_depth_1987_);
v___x_2092_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2048_, v_depth_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; uint8_t v___x_2094_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
v___x_2094_ = lean_unbox(v_a_2093_);
if (v___x_2094_ == 0)
{
lean_dec_ref(v_arg_2043_);
lean_dec(v_depth_1987_);
return v___x_2092_;
}
else
{
lean_object* v___x_2095_; 
lean_dec_ref_known(v___x_2092_, 1);
v___x_2095_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2043_, v_depth_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
return v___x_2095_;
}
}
else
{
lean_dec_ref(v_arg_2043_);
lean_dec(v_depth_1987_);
return v___x_2092_;
}
}
}
else
{
lean_dec_ref(v_arg_2048_);
lean_dec_ref(v_arg_2043_);
lean_dec(v_depth_1987_);
return v___x_2089_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2049_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_e_1986_);
v_p_2017_ = v_arg_2048_;
v_q_2018_ = v_arg_2043_;
v___y_2019_ = v_a_1988_;
v___y_2020_ = v_a_1989_;
v___y_2021_ = v_a_1990_;
v___y_2022_ = v_a_1991_;
v___y_2023_ = v_a_1992_;
v___y_2024_ = v_a_1993_;
v___y_2025_ = v_a_1994_;
v___y_2026_ = v_a_1995_;
v___y_2027_ = v_a_1996_;
goto v___jp_2016_;
}
}
else
{
lean_dec_ref(v___x_2049_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_e_1986_);
v_p_2017_ = v_arg_2048_;
v_q_2018_ = v_arg_2043_;
v___y_2019_ = v_a_1988_;
v___y_2020_ = v_a_1989_;
v___y_2021_ = v_a_1990_;
v___y_2022_ = v_a_1991_;
v___y_2023_ = v_a_1992_;
v___y_2024_ = v_a_1993_;
v___y_2025_ = v_a_1994_;
v___y_2026_ = v_a_1995_;
v___y_2027_ = v_a_1996_;
goto v___jp_2016_;
}
}
else
{
lean_dec_ref(v___x_2049_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_e_1986_);
v_p_2017_ = v_arg_2048_;
v_q_2018_ = v_arg_2043_;
v___y_2019_ = v_a_1988_;
v___y_2020_ = v_a_1989_;
v___y_2021_ = v_a_1990_;
v___y_2022_ = v_a_1991_;
v___y_2023_ = v_a_1992_;
v___y_2024_ = v_a_1993_;
v___y_2025_ = v_a_1994_;
v___y_2026_ = v_a_1995_;
v___y_2027_ = v_a_1996_;
goto v___jp_2016_;
}
}
else
{
lean_object* v___x_2096_; 
lean_dec_ref(v___x_2049_);
lean_dec_ref(v_arg_2043_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_e_1986_);
v___x_2096_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_2048_, v_depth_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
return v___x_2096_;
}
}
}
else
{
lean_object* v___x_2097_; 
lean_dec_ref(v___x_2044_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_e_1986_);
v___x_2097_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2043_, v_depth_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
return v___x_2097_;
}
}
}
else
{
lean_dec_ref(v___x_2037_);
lean_del_object(v___x_2035_);
lean_dec(v_depth_1987_);
lean_dec_ref(v_e_1986_);
goto v___jp_1998_;
}
}
else
{
lean_dec_ref(v___x_2037_);
lean_del_object(v___x_2035_);
lean_dec(v_depth_1987_);
lean_dec_ref(v_e_1986_);
goto v___jp_1998_;
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_depth_1987_);
lean_dec_ref(v_e_1986_);
v_a_2099_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2032_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2032_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
v___jp_1998_:
{
uint8_t v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = 1;
v___x_2000_ = lean_box(v___x_1999_);
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
return v___x_2001_;
}
v___jp_2002_:
{
lean_object* v___x_2012_; 
lean_inc_ref(v_e_1986_);
v___x_2012_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp(v_e_1986_, v_depth_1987_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v_depth_1987_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; uint8_t v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v___x_2014_ = lean_unbox(v_a_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_dec_ref_known(v___x_2012_, 1);
v___x_2015_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg(v_e_1986_, v___y_2008_, v___y_2010_, v___y_2011_);
return v___x_2015_;
}
else
{
lean_dec_ref(v_e_1986_);
return v___x_2012_;
}
}
else
{
lean_dec_ref(v_e_1986_);
return v___x_2012_;
}
}
v___jp_2016_:
{
lean_object* v___x_2028_; 
lean_inc(v_depth_1987_);
v___x_2028_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_p_2017_, v_depth_1987_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; uint8_t v___x_2030_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v___x_2030_ = lean_unbox(v_a_2029_);
if (v___x_2030_ == 0)
{
lean_dec_ref(v_q_2018_);
lean_dec(v_depth_1987_);
return v___x_2028_;
}
else
{
lean_object* v___x_2031_; 
lean_dec_ref_known(v___x_2028_, 1);
v___x_2031_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_q_2018_, v_depth_1987_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
return v___x_2031_;
}
}
else
{
lean_dec_ref(v_q_2018_);
lean_dec(v_depth_1987_);
return v___x_2028_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(lean_object* v_e_2107_, lean_object* v_depth_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v___x_2119_; lean_object* v_cache_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; uint8_t v___x_2123_; 
v___x_2119_ = lean_st_ref_get(v_a_2110_);
v_cache_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc_ref(v_cache_2120_);
lean_dec(v___x_2119_);
lean_inc(v_depth_2108_);
lean_inc_ref(v_e_2107_);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v_e_2107_);
lean_ctor_set(v___x_2121_, 1, v_depth_2108_);
v___x_2122_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg(v_cache_2120_, v___x_2121_);
lean_dec_ref(v_cache_2120_);
v___x_2123_ = 1;
if (v___x_2122_ == 0)
{
lean_object* v___x_2124_; 
v___x_2124_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go(v_e_2107_, v_depth_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; uint8_t v___x_2126_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v___x_2126_ = lean_unbox(v_a_2125_);
if (v___x_2126_ == 0)
{
lean_dec_ref_known(v___x_2121_, 2);
return v___x_2124_;
}
else
{
lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2147_; 
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; 
v_unused_2148_ = lean_ctor_get(v___x_2124_, 0);
lean_dec(v_unused_2148_);
v___x_2128_ = v___x_2124_;
v_isShared_2129_ = v_isSharedCheck_2147_;
goto v_resetjp_2127_;
}
else
{
lean_dec(v___x_2124_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2147_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; uint8_t v_mentionsSort_2131_; lean_object* v_cache_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2146_; 
v___x_2130_ = lean_st_ref_take(v_a_2110_);
v_mentionsSort_2131_ = lean_ctor_get_uint8(v___x_2130_, sizeof(void*)*1);
v_cache_2132_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2134_ = v___x_2130_;
v_isShared_2135_ = v_isSharedCheck_2146_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_cache_2132_);
lean_dec(v___x_2130_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2146_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2136_ = lean_box(0);
v___x_2137_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2___redArg(v_cache_2132_, v___x_2121_, v___x_2136_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2137_);
v___x_2139_ = v___x_2134_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2137_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*1, v_mentionsSort_2131_);
v___x_2139_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2140_ = lean_st_ref_put(v_a_2110_, v___x_2139_);
v___x_2141_ = lean_box(v___x_2123_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2141_);
v___x_2143_ = v___x_2128_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2121_, 2);
return v___x_2124_;
}
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_dec_ref_known(v___x_2121_, 2);
lean_dec(v_depth_2108_);
lean_dec_ref(v_e_2107_);
v___x_2149_ = lean_box(v___x_2123_);
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
return v___x_2150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool___boxed(lean_object* v_e_2151_, lean_object* v_depth_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_e_2151_, v_depth_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
lean_dec(v_a_2157_);
lean_dec_ref(v_a_2156_);
lean_dec(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp___boxed(lean_object* v_e_2164_, lean_object* v_depth_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_e_2164_, v_depth_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_dec(v_a_2168_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___boxed(lean_object* v_e_2177_, lean_object* v_depth_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go(v_e_2177_, v_depth_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
lean_dec(v_a_2185_);
lean_dec_ref(v_a_2184_);
lean_dec(v_a_2183_);
lean_dec_ref(v_a_2182_);
lean_dec(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___boxed(lean_object* v_e_2190_, lean_object* v_depth_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go(v_e_2190_, v_depth_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
return v_res_2202_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1(lean_object* v_00_u03b2_2203_, lean_object* v_m_2204_, lean_object* v_a_2205_){
_start:
{
uint8_t v___x_2206_; 
v___x_2206_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg(v_m_2204_, v_a_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___boxed(lean_object* v_00_u03b2_2207_, lean_object* v_m_2208_, lean_object* v_a_2209_){
_start:
{
uint8_t v_res_2210_; lean_object* v_r_2211_; 
v_res_2210_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1(v_00_u03b2_2207_, v_m_2208_, v_a_2209_);
lean_dec_ref(v_a_2209_);
lean_dec_ref(v_m_2208_);
v_r_2211_ = lean_box(v_res_2210_);
return v_r_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2(lean_object* v_00_u03b2_2212_, lean_object* v_m_2213_, lean_object* v_a_2214_, lean_object* v_b_2215_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2___redArg(v_m_2213_, v_a_2214_, v_b_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2(lean_object* v_00_u03b2_2217_, lean_object* v_a_2218_, lean_object* v_x_2219_){
_start:
{
uint8_t v___x_2220_; 
v___x_2220_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg(v_a_2218_, v_x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2221_, lean_object* v_a_2222_, lean_object* v_x_2223_){
_start:
{
uint8_t v_res_2224_; lean_object* v_r_2225_; 
v_res_2224_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2(v_00_u03b2_2221_, v_a_2222_, v_x_2223_);
lean_dec(v_x_2223_);
lean_dec_ref(v_a_2222_);
v_r_2225_ = lean_box(v_res_2224_);
return v_r_2225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4(lean_object* v_00_u03b2_2226_, lean_object* v_data_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4___redArg(v_data_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_2229_, lean_object* v_i_2230_, lean_object* v_source_2231_, lean_object* v_target_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6___redArg(v_i_2230_, v_source_2231_, v_target_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_2234_, lean_object* v_x_2235_, lean_object* v_x_2236_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6_spec__7___redArg(v_x_2235_, v_x_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___redArg(lean_object* v_type_2238_, lean_object* v_acc_2239_, lean_object* v_a_2240_){
_start:
{
if (lean_obj_tag(v_type_2238_) == 7)
{
lean_object* v_binderType_2242_; lean_object* v_body_2243_; lean_object* v___x_2244_; lean_object* v_sortIds_2245_; lean_object* v___x_2246_; 
v_binderType_2242_ = lean_ctor_get(v_type_2238_, 1);
v_body_2243_ = lean_ctor_get(v_type_2238_, 2);
v___x_2244_ = lean_st_ref_get(v_a_2240_);
v_sortIds_2245_ = lean_ctor_get(v___x_2244_, 1);
lean_inc_ref(v_sortIds_2245_);
lean_dec(v___x_2244_);
v___x_2246_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_sortIds_2245_, v_binderType_2242_);
lean_dec_ref(v_sortIds_2245_);
if (lean_obj_tag(v___x_2246_) == 1)
{
lean_object* v_val_2247_; lean_object* v___x_2248_; 
lean_inc_ref(v_body_2243_);
lean_dec_ref_known(v_type_2238_, 3);
v_val_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_val_2247_);
lean_dec_ref_known(v___x_2246_, 1);
v___x_2248_ = lean_array_push(v_acc_2239_, v_val_2247_);
v_type_2238_ = v_body_2243_;
v_acc_2239_ = v___x_2248_;
goto _start;
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_dec(v___x_2246_);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v_acc_2239_);
lean_ctor_set(v___x_2250_, 1, v_type_2238_);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
return v___x_2251_;
}
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v_acc_2239_);
lean_ctor_set(v___x_2252_, 1, v_type_2238_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___redArg___boxed(lean_object* v_type_2254_, lean_object* v_acc_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___redArg(v_type_2254_, v_acc_2255_, v_a_2256_);
lean_dec(v_a_2256_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers(lean_object* v_type_2259_, lean_object* v_acc_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___redArg(v_type_2259_, v_acc_2260_, v_a_2261_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___boxed(lean_object* v_type_2270_, lean_object* v_acc_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers(v_type_2270_, v_acc_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
lean_dec(v_a_2272_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0_spec__1(lean_object* v_msg_2281_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default;
v___x_2283_ = lean_panic_fn_borrowed(v___x_2282_, v_msg_2281_);
return v___x_2283_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2287_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__2));
v___x_2288_ = lean_unsigned_to_nat(11u);
v___x_2289_ = lean_unsigned_to_nat(163u);
v___x_2290_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__1));
v___x_2291_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__0));
v___x_2292_ = l_mkPanicMessageWithDecl(v___x_2291_, v___x_2290_, v___x_2289_, v___x_2288_, v___x_2287_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0(lean_object* v_a_2293_, lean_object* v_x_2294_){
_start:
{
if (lean_obj_tag(v_x_2294_) == 0)
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__3);
v___x_2296_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0_spec__1(v___x_2295_);
return v___x_2296_;
}
else
{
lean_object* v_key_2297_; lean_object* v_value_2298_; lean_object* v_tail_2299_; uint8_t v___x_2300_; 
v_key_2297_ = lean_ctor_get(v_x_2294_, 0);
v_value_2298_ = lean_ctor_get(v_x_2294_, 1);
v_tail_2299_ = lean_ctor_get(v_x_2294_, 2);
v___x_2300_ = lean_nat_dec_eq(v_key_2297_, v_a_2293_);
if (v___x_2300_ == 0)
{
v_x_2294_ = v_tail_2299_;
goto _start;
}
else
{
lean_inc(v_value_2298_);
return v_value_2298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___boxed(lean_object* v_a_2302_, lean_object* v_x_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0(v_a_2302_, v_x_2303_);
lean_dec(v_x_2303_);
lean_dec(v_a_2302_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0(lean_object* v_m_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_buckets_2307_; lean_object* v___x_2308_; uint64_t v___x_2309_; uint64_t v___x_2310_; uint64_t v___x_2311_; uint64_t v_fold_2312_; uint64_t v___x_2313_; uint64_t v___x_2314_; uint64_t v___x_2315_; size_t v___x_2316_; size_t v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_buckets_2307_ = lean_ctor_get(v_m_2305_, 1);
v___x_2308_ = lean_array_get_size(v_buckets_2307_);
v___x_2309_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_a_2306_);
v___x_2310_ = 32ULL;
v___x_2311_ = lean_uint64_shift_right(v___x_2309_, v___x_2310_);
v_fold_2312_ = lean_uint64_xor(v___x_2309_, v___x_2311_);
v___x_2313_ = 16ULL;
v___x_2314_ = lean_uint64_shift_right(v_fold_2312_, v___x_2313_);
v___x_2315_ = lean_uint64_xor(v_fold_2312_, v___x_2314_);
v___x_2316_ = lean_uint64_to_usize(v___x_2315_);
v___x_2317_ = lean_usize_of_nat(v___x_2308_);
v___x_2318_ = ((size_t)1ULL);
v___x_2319_ = lean_usize_sub(v___x_2317_, v___x_2318_);
v___x_2320_ = lean_usize_land(v___x_2316_, v___x_2319_);
v___x_2321_ = lean_array_uget_borrowed(v_buckets_2307_, v___x_2320_);
v___x_2322_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0(v_a_2306_, v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0___boxed(lean_object* v_m_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0(v_m_2323_, v_a_2324_);
lean_dec(v_a_2324_);
lean_dec_ref(v_m_2323_);
return v_res_2325_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1(lean_object* v___x_2326_, lean_object* v_as_2327_, size_t v_i_2328_, size_t v_stop_2329_){
_start:
{
uint8_t v___x_2330_; 
v___x_2330_ = lean_usize_dec_eq(v_i_2328_, v_stop_2329_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v_elements_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2331_ = lean_array_uget_borrowed(v_as_2327_, v_i_2328_);
v___x_2332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0(v___x_2326_, v___x_2331_);
v_elements_2333_ = lean_ctor_get(v___x_2332_, 2);
lean_inc_ref(v_elements_2333_);
lean_dec_ref(v___x_2332_);
v___x_2334_ = lean_array_get_size(v_elements_2333_);
lean_dec_ref(v_elements_2333_);
v___x_2335_ = lean_unsigned_to_nat(0u);
v___x_2336_ = lean_nat_dec_eq(v___x_2334_, v___x_2335_);
if (v___x_2336_ == 0)
{
size_t v___x_2337_; size_t v___x_2338_; 
v___x_2337_ = ((size_t)1ULL);
v___x_2338_ = lean_usize_add(v_i_2328_, v___x_2337_);
v_i_2328_ = v___x_2338_;
goto _start;
}
else
{
return v___x_2336_;
}
}
else
{
uint8_t v___x_2340_; 
v___x_2340_ = 0;
return v___x_2340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1___boxed(lean_object* v___x_2341_, lean_object* v_as_2342_, lean_object* v_i_2343_, lean_object* v_stop_2344_){
_start:
{
size_t v_i_boxed_2345_; size_t v_stop_boxed_2346_; uint8_t v_res_2347_; lean_object* v_r_2348_; 
v_i_boxed_2345_ = lean_unbox_usize(v_i_2343_);
lean_dec(v_i_2343_);
v_stop_boxed_2346_ = lean_unbox_usize(v_stop_2344_);
lean_dec(v_stop_2344_);
v_res_2347_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1(v___x_2341_, v_as_2342_, v_i_boxed_2345_, v_stop_boxed_2346_);
lean_dec_ref(v_as_2342_);
lean_dec_ref(v___x_2341_);
v_r_2348_ = lean_box(v_res_2347_);
return v_r_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2_spec__3(lean_object* v_msgData_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; lean_object* v_env_2356_; uint8_t v___x_2357_; lean_object* v_env_2358_; lean_object* v___x_2359_; lean_object* v_toCold_2360_; lean_object* v_mctx_2361_; lean_object* v_lctx_2362_; lean_object* v_options_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2355_ = lean_st_ref_get(v___y_2353_);
v_env_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc_ref(v_env_2356_);
lean_dec(v___x_2355_);
v___x_2357_ = 0;
v_env_2358_ = l_Lean_Environment_setRecordingDeps(v_env_2356_, v___x_2357_);
v___x_2359_ = lean_st_ref_get(v___y_2351_);
v_toCold_2360_ = lean_ctor_get(v___y_2352_, 0);
v_mctx_2361_ = lean_ctor_get(v___x_2359_, 0);
lean_inc_ref(v_mctx_2361_);
lean_dec(v___x_2359_);
v_lctx_2362_ = lean_ctor_get(v___y_2350_, 2);
v_options_2363_ = lean_ctor_get(v_toCold_2360_, 2);
lean_inc_ref(v_options_2363_);
lean_inc_ref(v_lctx_2362_);
v___x_2364_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2364_, 0, v_env_2358_);
lean_ctor_set(v___x_2364_, 1, v_mctx_2361_);
lean_ctor_set(v___x_2364_, 2, v_lctx_2362_);
lean_ctor_set(v___x_2364_, 3, v_options_2363_);
v___x_2365_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
lean_ctor_set(v___x_2365_, 1, v_msgData_2349_);
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2_spec__3___boxed(lean_object* v_msgData_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2_spec__3(v_msgData_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
return v_res_2373_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2374_; double v___x_2375_; 
v___x_2374_ = lean_unsigned_to_nat(0u);
v___x_2375_ = lean_float_of_nat(v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg(lean_object* v_cls_2379_, lean_object* v_msg_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v_ref_2386_; lean_object* v___x_2387_; lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2433_; 
v_ref_2386_ = lean_ctor_get(v___y_2383_, 2);
v___x_2387_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2_spec__3(v_msg_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2433_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2433_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v_traceState_2393_; lean_object* v_env_2394_; lean_object* v_nextMacroScope_2395_; lean_object* v_ngen_2396_; lean_object* v_auxDeclNGen_2397_; lean_object* v_cache_2398_; lean_object* v_recordedDeps_2399_; lean_object* v_messages_2400_; lean_object* v_infoState_2401_; lean_object* v_snapshotTasks_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2432_; 
v___x_2392_ = lean_st_ref_take(v___y_2384_);
v_traceState_2393_ = lean_ctor_get(v___x_2392_, 4);
v_env_2394_ = lean_ctor_get(v___x_2392_, 0);
v_nextMacroScope_2395_ = lean_ctor_get(v___x_2392_, 1);
v_ngen_2396_ = lean_ctor_get(v___x_2392_, 2);
v_auxDeclNGen_2397_ = lean_ctor_get(v___x_2392_, 3);
v_cache_2398_ = lean_ctor_get(v___x_2392_, 5);
v_recordedDeps_2399_ = lean_ctor_get(v___x_2392_, 6);
v_messages_2400_ = lean_ctor_get(v___x_2392_, 7);
v_infoState_2401_ = lean_ctor_get(v___x_2392_, 8);
v_snapshotTasks_2402_ = lean_ctor_get(v___x_2392_, 9);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2404_ = v___x_2392_;
v_isShared_2405_ = v_isSharedCheck_2432_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_snapshotTasks_2402_);
lean_inc(v_infoState_2401_);
lean_inc(v_messages_2400_);
lean_inc(v_recordedDeps_2399_);
lean_inc(v_cache_2398_);
lean_inc(v_traceState_2393_);
lean_inc(v_auxDeclNGen_2397_);
lean_inc(v_ngen_2396_);
lean_inc(v_nextMacroScope_2395_);
lean_inc(v_env_2394_);
lean_dec(v___x_2392_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2432_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
uint64_t v_tid_2406_; lean_object* v_traces_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2431_; 
v_tid_2406_ = lean_ctor_get_uint64(v_traceState_2393_, sizeof(void*)*1);
v_traces_2407_ = lean_ctor_get(v_traceState_2393_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_traceState_2393_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2409_ = v_traceState_2393_;
v_isShared_2410_ = v_isSharedCheck_2431_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_traces_2407_);
lean_dec(v_traceState_2393_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2431_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; double v___x_2413_; uint8_t v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2411_ = lean_box(0);
v___x_2412_ = lean_box(0);
v___x_2413_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0);
v___x_2414_ = 0;
v___x_2415_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__1));
v___x_2416_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2416_, 0, v_cls_2379_);
lean_ctor_set(v___x_2416_, 1, v___x_2412_);
lean_ctor_set(v___x_2416_, 2, v___x_2415_);
lean_ctor_set_float(v___x_2416_, sizeof(void*)*3, v___x_2413_);
lean_ctor_set_float(v___x_2416_, sizeof(void*)*3 + 8, v___x_2413_);
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*3 + 16, v___x_2414_);
v___x_2417_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__2));
v___x_2418_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v_a_2388_);
lean_ctor_set(v___x_2418_, 2, v___x_2417_);
lean_inc(v_ref_2386_);
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v_ref_2386_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
v___x_2420_ = l_Lean_PersistentArray_push___redArg(v_traces_2407_, v___x_2419_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v___x_2420_);
v___x_2422_ = v___x_2409_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2420_);
lean_ctor_set_uint64(v_reuseFailAlloc_2430_, sizeof(void*)*1, v_tid_2406_);
v___x_2422_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2424_; 
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 4, v___x_2422_);
v___x_2424_ = v___x_2404_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_env_2394_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v_nextMacroScope_2395_);
lean_ctor_set(v_reuseFailAlloc_2429_, 2, v_ngen_2396_);
lean_ctor_set(v_reuseFailAlloc_2429_, 3, v_auxDeclNGen_2397_);
lean_ctor_set(v_reuseFailAlloc_2429_, 4, v___x_2422_);
lean_ctor_set(v_reuseFailAlloc_2429_, 5, v_cache_2398_);
lean_ctor_set(v_reuseFailAlloc_2429_, 6, v_recordedDeps_2399_);
lean_ctor_set(v_reuseFailAlloc_2429_, 7, v_messages_2400_);
lean_ctor_set(v_reuseFailAlloc_2429_, 8, v_infoState_2401_);
lean_ctor_set(v_reuseFailAlloc_2429_, 9, v_snapshotTasks_2402_);
v___x_2424_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2425_ = lean_st_ref_put(v___y_2384_, v___x_2424_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2411_);
v___x_2427_ = v___x_2390_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2411_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___boxed(lean_object* v_cls_2434_, lean_object* v_msg_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg(v_cls_2434_, v_msg_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
return v_res_2441_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__0(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = lean_box(0);
v___x_2443_ = lean_unsigned_to_nat(16u);
v___x_2444_ = lean_mk_array(v___x_2443_, v___x_2442_);
return v___x_2444_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__1(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__0);
v___x_2446_ = lean_unsigned_to_nat(0u);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
lean_ctor_set(v___x_2447_, 1, v___x_2445_);
return v___x_2447_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9(void){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_2461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__8));
v___x_2462_ = l_Lean_Name_append(v___x_2461_, v___x_2460_);
return v___x_2462_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__11(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__10));
v___x_2465_ = l_Lean_stringToMessageData(v___x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f(lean_object* v_hyp_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_type_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2548_; 
v_type_2481_ = lean_ctor_get(v_hyp_2466_, 1);
lean_inc_ref_n(v_type_2481_, 2);
lean_dec_ref(v_hyp_2466_);
v___x_2482_ = lean_unsigned_to_nat(0u);
v___x_2483_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg___closed__0));
v___x_2484_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___redArg(v_type_2481_, v___x_2483_, v_a_2467_);
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2548_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2548_;
goto v_resetjp_2486_;
}
v___jp_2475_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_box(0);
v___x_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
return v___x_2477_;
}
v___jp_2478_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = lean_box(0);
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
v_resetjp_2486_:
{
lean_object* v_fst_2489_; lean_object* v_snd_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2547_; 
v_fst_2489_ = lean_ctor_get(v_a_2485_, 0);
v_snd_2490_ = lean_ctor_get(v_a_2485_, 1);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_a_2485_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2492_ = v_a_2485_;
v_isShared_2493_ = v_isSharedCheck_2547_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_snd_2490_);
lean_inc(v_fst_2489_);
lean_dec(v_a_2485_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2547_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2499_; uint8_t v___y_2501_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v___x_2499_ = lean_st_ref_get(v_a_2467_);
v___x_2520_ = lean_array_get_size(v_fst_2489_);
v___x_2521_ = lean_nat_dec_lt(v___x_2482_, v___x_2520_);
if (v___x_2521_ == 0)
{
lean_dec(v___x_2499_);
lean_del_object(v___x_2492_);
lean_dec_ref(v_type_2481_);
v___y_2501_ = v___x_2521_;
goto v___jp_2500_;
}
else
{
if (v___x_2521_ == 0)
{
lean_dec(v___x_2499_);
lean_del_object(v___x_2492_);
lean_dec_ref(v_type_2481_);
v___y_2501_ = v___x_2521_;
goto v___jp_2500_;
}
else
{
lean_object* v_sorts_2522_; size_t v___x_2523_; size_t v___x_2524_; uint8_t v___x_2525_; 
v_sorts_2522_ = lean_ctor_get(v___x_2499_, 0);
lean_inc_ref(v_sorts_2522_);
lean_dec(v___x_2499_);
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = lean_usize_of_nat(v___x_2520_);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1(v_sorts_2522_, v_fst_2489_, v___x_2523_, v___x_2524_);
lean_dec_ref(v_sorts_2522_);
if (v___x_2525_ == 0)
{
lean_del_object(v___x_2492_);
lean_dec_ref(v_type_2481_);
v___y_2501_ = v___x_2525_;
goto v___jp_2500_;
}
else
{
lean_object* v_toCold_2526_; lean_object* v_options_2527_; uint8_t v_hasTrace_2528_; 
lean_dec(v_snd_2490_);
lean_dec(v_fst_2489_);
lean_del_object(v___x_2487_);
v_toCold_2526_ = lean_ctor_get(v_a_2472_, 0);
v_options_2527_ = lean_ctor_get(v_toCold_2526_, 2);
v_hasTrace_2528_ = lean_ctor_get_uint8(v_options_2527_, sizeof(void*)*1);
if (v_hasTrace_2528_ == 0)
{
lean_del_object(v___x_2492_);
lean_dec_ref(v_type_2481_);
goto v___jp_2475_;
}
else
{
lean_object* v_inheritedTraceOptions_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v_inheritedTraceOptions_2529_ = lean_ctor_get(v_toCold_2526_, 11);
v___x_2530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_2531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9);
v___x_2532_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2529_, v_options_2527_, v___x_2531_);
if (v___x_2532_ == 0)
{
lean_del_object(v___x_2492_);
lean_dec_ref(v_type_2481_);
goto v___jp_2475_;
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
v___x_2533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__11, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__11);
v___x_2534_ = l_Lean_MessageData_ofExpr(v_type_2481_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set_tag(v___x_2492_, 7);
lean_ctor_set(v___x_2492_, 1, v___x_2534_);
lean_ctor_set(v___x_2492_, 0, v___x_2533_);
v___x_2536_ = v___x_2492_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg(v___x_2530_, v___x_2536_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref_known(v___x_2537_, 1);
goto v___jp_2475_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
}
}
}
}
v___jp_2494_:
{
lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2495_, 0, v_fst_2489_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2495_);
v___x_2497_ = v___x_2487_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
v___jp_2500_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2502_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__1);
v___x_2503_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set_uint8(v___x_2503_, sizeof(void*)*1, v___y_2501_);
v___x_2504_ = lean_st_mk_ref(v___x_2503_);
v___x_2505_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_snd_2490_, v___x_2482_, v_fst_2489_, v___x_2504_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2507_ = lean_st_ref_get(v___x_2504_);
lean_dec(v___x_2504_);
v___x_2508_ = lean_unbox(v_a_2506_);
lean_dec(v_a_2506_);
if (v___x_2508_ == 0)
{
lean_dec(v___x_2507_);
lean_dec(v_fst_2489_);
lean_del_object(v___x_2487_);
goto v___jp_2478_;
}
else
{
if (v___y_2501_ == 0)
{
uint8_t v_mentionsSort_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; 
v_mentionsSort_2509_ = lean_ctor_get_uint8(v___x_2507_, sizeof(void*)*1);
lean_dec(v___x_2507_);
v___x_2510_ = lean_array_get_size(v_fst_2489_);
v___x_2511_ = lean_nat_dec_eq(v___x_2510_, v___x_2482_);
if (v___x_2511_ == 0)
{
goto v___jp_2494_;
}
else
{
if (v_mentionsSort_2509_ == 0)
{
lean_dec(v_fst_2489_);
lean_del_object(v___x_2487_);
goto v___jp_2478_;
}
else
{
goto v___jp_2494_;
}
}
}
else
{
lean_dec(v___x_2507_);
lean_dec(v_fst_2489_);
lean_del_object(v___x_2487_);
goto v___jp_2478_;
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec(v___x_2504_);
lean_dec(v_fst_2489_);
lean_del_object(v___x_2487_);
v_a_2512_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2505_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2505_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___boxed(lean_object* v_hyp_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f(v_hyp_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
lean_dec(v_a_2556_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2(lean_object* v_cls_2559_, lean_object* v_msg_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg(v_cls_2559_, v_msg_2560_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___boxed(lean_object* v_cls_2570_, lean_object* v_msg_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2(v_cls_2570_, v_msg_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processHyp(lean_object* v_hyp_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v___x_2590_; 
lean_inc_ref(v_hyp_2581_);
v___x_2590_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f(v_hyp_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2666_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2666_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2666_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
if (lean_obj_tag(v_a_2591_) == 0)
{
lean_object* v___x_2595_; lean_object* v_sorts_2596_; lean_object* v_sortIds_2597_; lean_object* v_nextSortId_2598_; lean_object* v_elements_2599_; lean_object* v_preds_2600_; lean_object* v_groundFacts_2601_; lean_object* v_quantifiedFacts_2602_; lean_object* v_remainingHyps_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2616_; 
v___x_2595_ = lean_st_ref_take(v_a_2582_);
v_sorts_2596_ = lean_ctor_get(v___x_2595_, 0);
v_sortIds_2597_ = lean_ctor_get(v___x_2595_, 1);
v_nextSortId_2598_ = lean_ctor_get(v___x_2595_, 2);
v_elements_2599_ = lean_ctor_get(v___x_2595_, 3);
v_preds_2600_ = lean_ctor_get(v___x_2595_, 4);
v_groundFacts_2601_ = lean_ctor_get(v___x_2595_, 5);
v_quantifiedFacts_2602_ = lean_ctor_get(v___x_2595_, 6);
v_remainingHyps_2603_ = lean_ctor_get(v___x_2595_, 7);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2605_ = v___x_2595_;
v_isShared_2606_ = v_isSharedCheck_2616_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_remainingHyps_2603_);
lean_inc(v_quantifiedFacts_2602_);
lean_inc(v_groundFacts_2601_);
lean_inc(v_preds_2600_);
lean_inc(v_elements_2599_);
lean_inc(v_nextSortId_2598_);
lean_inc(v_sortIds_2597_);
lean_inc(v_sorts_2596_);
lean_dec(v___x_2595_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2616_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2610_; 
v___x_2607_ = lean_box(0);
v___x_2608_ = lean_array_push(v_remainingHyps_2603_, v_hyp_2581_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 7, v___x_2608_);
v___x_2610_ = v___x_2605_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_sorts_2596_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_sortIds_2597_);
lean_ctor_set(v_reuseFailAlloc_2615_, 2, v_nextSortId_2598_);
lean_ctor_set(v_reuseFailAlloc_2615_, 3, v_elements_2599_);
lean_ctor_set(v_reuseFailAlloc_2615_, 4, v_preds_2600_);
lean_ctor_set(v_reuseFailAlloc_2615_, 5, v_groundFacts_2601_);
lean_ctor_set(v_reuseFailAlloc_2615_, 6, v_quantifiedFacts_2602_);
lean_ctor_set(v_reuseFailAlloc_2615_, 7, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_st_ref_put(v_a_2582_, v___x_2610_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2607_);
v___x_2613_ = v___x_2593_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2607_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_object* v_val_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; uint8_t v___x_2620_; 
v_val_2617_ = lean_ctor_get(v_a_2591_, 0);
lean_inc(v_val_2617_);
lean_dec_ref_known(v_a_2591_, 1);
v___x_2618_ = lean_array_get_size(v_val_2617_);
v___x_2619_ = lean_unsigned_to_nat(0u);
v___x_2620_ = lean_nat_dec_eq(v___x_2618_, v___x_2619_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; lean_object* v_sorts_2622_; lean_object* v_sortIds_2623_; lean_object* v_nextSortId_2624_; lean_object* v_elements_2625_; lean_object* v_preds_2626_; lean_object* v_groundFacts_2627_; lean_object* v_quantifiedFacts_2628_; lean_object* v_remainingHyps_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2643_; 
v___x_2621_ = lean_st_ref_take(v_a_2582_);
v_sorts_2622_ = lean_ctor_get(v___x_2621_, 0);
v_sortIds_2623_ = lean_ctor_get(v___x_2621_, 1);
v_nextSortId_2624_ = lean_ctor_get(v___x_2621_, 2);
v_elements_2625_ = lean_ctor_get(v___x_2621_, 3);
v_preds_2626_ = lean_ctor_get(v___x_2621_, 4);
v_groundFacts_2627_ = lean_ctor_get(v___x_2621_, 5);
v_quantifiedFacts_2628_ = lean_ctor_get(v___x_2621_, 6);
v_remainingHyps_2629_ = lean_ctor_get(v___x_2621_, 7);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2631_ = v___x_2621_;
v_isShared_2632_ = v_isSharedCheck_2643_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_remainingHyps_2629_);
lean_inc(v_quantifiedFacts_2628_);
lean_inc(v_groundFacts_2627_);
lean_inc(v_preds_2626_);
lean_inc(v_elements_2625_);
lean_inc(v_nextSortId_2624_);
lean_inc(v_sortIds_2623_);
lean_inc(v_sorts_2622_);
lean_dec(v___x_2621_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2643_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; 
v___x_2633_ = lean_box(0);
v___x_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2634_, 0, v_hyp_2581_);
lean_ctor_set(v___x_2634_, 1, v_val_2617_);
v___x_2635_ = lean_array_push(v_quantifiedFacts_2628_, v___x_2634_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 6, v___x_2635_);
v___x_2637_ = v___x_2631_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_sorts_2622_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_sortIds_2623_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v_nextSortId_2624_);
lean_ctor_set(v_reuseFailAlloc_2642_, 3, v_elements_2625_);
lean_ctor_set(v_reuseFailAlloc_2642_, 4, v_preds_2626_);
lean_ctor_set(v_reuseFailAlloc_2642_, 5, v_groundFacts_2627_);
lean_ctor_set(v_reuseFailAlloc_2642_, 6, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2642_, 7, v_remainingHyps_2629_);
v___x_2637_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2638_ = lean_st_ref_put(v_a_2582_, v___x_2637_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2633_);
v___x_2640_ = v___x_2593_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2633_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v___x_2644_; lean_object* v_sorts_2645_; lean_object* v_sortIds_2646_; lean_object* v_nextSortId_2647_; lean_object* v_elements_2648_; lean_object* v_preds_2649_; lean_object* v_groundFacts_2650_; lean_object* v_quantifiedFacts_2651_; lean_object* v_remainingHyps_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v_val_2617_);
v___x_2644_ = lean_st_ref_take(v_a_2582_);
v_sorts_2645_ = lean_ctor_get(v___x_2644_, 0);
v_sortIds_2646_ = lean_ctor_get(v___x_2644_, 1);
v_nextSortId_2647_ = lean_ctor_get(v___x_2644_, 2);
v_elements_2648_ = lean_ctor_get(v___x_2644_, 3);
v_preds_2649_ = lean_ctor_get(v___x_2644_, 4);
v_groundFacts_2650_ = lean_ctor_get(v___x_2644_, 5);
v_quantifiedFacts_2651_ = lean_ctor_get(v___x_2644_, 6);
v_remainingHyps_2652_ = lean_ctor_get(v___x_2644_, 7);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2654_ = v___x_2644_;
v_isShared_2655_ = v_isSharedCheck_2665_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_remainingHyps_2652_);
lean_inc(v_quantifiedFacts_2651_);
lean_inc(v_groundFacts_2650_);
lean_inc(v_preds_2649_);
lean_inc(v_elements_2648_);
lean_inc(v_nextSortId_2647_);
lean_inc(v_sortIds_2646_);
lean_inc(v_sorts_2645_);
lean_dec(v___x_2644_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2665_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2656_ = lean_box(0);
v___x_2657_ = lean_array_push(v_groundFacts_2650_, v_hyp_2581_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 5, v___x_2657_);
v___x_2659_ = v___x_2654_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_sorts_2645_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_sortIds_2646_);
lean_ctor_set(v_reuseFailAlloc_2664_, 2, v_nextSortId_2647_);
lean_ctor_set(v_reuseFailAlloc_2664_, 3, v_elements_2648_);
lean_ctor_set(v_reuseFailAlloc_2664_, 4, v_preds_2649_);
lean_ctor_set(v_reuseFailAlloc_2664_, 5, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2664_, 6, v_quantifiedFacts_2651_);
lean_ctor_set(v_reuseFailAlloc_2664_, 7, v_remainingHyps_2652_);
v___x_2659_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2660_ = lean_st_ref_put(v_a_2582_, v___x_2659_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2656_);
v___x_2662_ = v___x_2593_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2656_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec_ref(v_hyp_2581_);
v_a_2667_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2590_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2590_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processHyp___boxed(lean_object* v_hyp_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processHyp(v_hyp_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0(lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
if (lean_obj_tag(v_a_2693_) == 0)
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_a_2694_);
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
return v___x_2704_;
}
else
{
lean_object* v_value_2705_; lean_object* v_key_2706_; lean_object* v_tail_2707_; lean_object* v_type_2708_; lean_object* v_level_2709_; lean_object* v_elements_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v_value_2705_ = lean_ctor_get(v_a_2693_, 1);
lean_inc(v_value_2705_);
v_key_2706_ = lean_ctor_get(v_a_2693_, 0);
lean_inc(v_key_2706_);
v_tail_2707_ = lean_ctor_get(v_a_2693_, 2);
lean_inc(v_tail_2707_);
lean_dec_ref_known(v_a_2693_, 3);
v_type_2708_ = lean_ctor_get(v_value_2705_, 0);
lean_inc_ref(v_type_2708_);
v_level_2709_ = lean_ctor_get(v_value_2705_, 1);
lean_inc(v_level_2709_);
v_elements_2710_ = lean_ctor_get(v_value_2705_, 2);
lean_inc_ref(v_elements_2710_);
lean_dec(v_value_2705_);
v___x_2711_ = lean_box(0);
v___x_2712_ = lean_array_get_size(v_elements_2710_);
lean_dec_ref(v_elements_2710_);
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = lean_nat_dec_eq(v___x_2712_, v___x_2713_);
if (v___x_2714_ == 0)
{
lean_dec(v_level_2709_);
lean_dec_ref(v_type_2708_);
lean_dec(v_key_2706_);
v_a_2693_ = v_tail_2707_;
v_a_2694_ = v___x_2711_;
goto _start;
}
else
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2716_ = l_Lean_Level_succ___override(v_level_2709_);
v___x_2717_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__1));
v___x_2718_ = lean_box(0);
v___x_2719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2716_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
lean_inc_ref(v___x_2719_);
v___x_2720_ = l_Lean_mkConst(v___x_2717_, v___x_2719_);
lean_inc_ref(v_type_2708_);
v___x_2721_ = l_Lean_Expr_app___override(v___x_2720_, v_type_2708_);
v___x_2722_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2721_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2724_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v___x_2722_, 1);
v___x_2724_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_2723_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2724_, 1);
if (lean_obj_tag(v_a_2725_) == 1)
{
lean_object* v_val_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_val_2726_ = lean_ctor_get(v_a_2725_, 0);
lean_inc(v_val_2726_);
lean_dec_ref_known(v_a_2725_, 1);
v___x_2727_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__4));
v___x_2728_ = l_Lean_mkConst(v___x_2727_, v___x_2719_);
v___x_2729_ = l_Lean_mkAppB(v___x_2728_, v_type_2708_, v_val_2726_);
v___x_2730_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2729_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2732_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v___x_2732_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg(v_a_2731_, v_key_2706_, v___y_2695_);
lean_dec_ref(v___x_2732_);
v_a_2693_ = v_tail_2707_;
v_a_2694_ = v___x_2711_;
goto _start;
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_tail_2707_);
lean_dec(v_key_2706_);
v_a_2734_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2730_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2730_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_dec(v_a_2725_);
lean_dec_ref_known(v___x_2719_, 2);
lean_dec_ref(v_type_2708_);
lean_dec(v_key_2706_);
v_a_2693_ = v_tail_2707_;
v_a_2694_ = v___x_2711_;
goto _start;
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref_known(v___x_2719_, 2);
lean_dec_ref(v_type_2708_);
lean_dec(v_tail_2707_);
lean_dec(v_key_2706_);
v_a_2743_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2724_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2724_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec_ref_known(v___x_2719_, 2);
lean_dec_ref(v_type_2708_);
lean_dec(v_tail_2707_);
lean_dec(v_key_2706_);
v_a_2751_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2722_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2722_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___boxed(lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0(v_a_2759_, v_a_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__1(lean_object* v_as_2770_, size_t v_sz_2771_, size_t v_i_2772_, lean_object* v_b_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
uint8_t v___x_2782_; 
v___x_2782_ = lean_usize_dec_lt(v_i_2772_, v_sz_2771_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2783_, 0, v_b_2773_);
return v___x_2783_;
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2785_; 
v_a_2784_ = lean_array_uget_borrowed(v_as_2770_, v_i_2772_);
lean_inc(v_a_2784_);
v___x_2785_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0(v_a_2784_, v_b_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2798_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2788_ = v___x_2785_;
v_isShared_2789_ = v_isSharedCheck_2798_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2785_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2798_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
if (lean_obj_tag(v_a_2786_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; 
v_a_2790_ = lean_ctor_get(v_a_2786_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v_a_2786_, 1);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v_a_2790_);
v___x_2792_ = v___x_2788_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2790_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
else
{
lean_object* v_a_2794_; size_t v___x_2795_; size_t v___x_2796_; 
lean_del_object(v___x_2788_);
v_a_2794_ = lean_ctor_get(v_a_2786_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v_a_2786_, 1);
v___x_2795_ = ((size_t)1ULL);
v___x_2796_ = lean_usize_add(v_i_2772_, v___x_2795_);
v_i_2772_ = v___x_2796_;
v_b_2773_ = v_a_2794_;
goto _start;
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
v_a_2799_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2785_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2785_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__1___boxed(lean_object* v_as_2807_, lean_object* v_sz_2808_, lean_object* v_i_2809_, lean_object* v_b_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
size_t v_sz_boxed_2819_; size_t v_i_boxed_2820_; lean_object* v_res_2821_; 
v_sz_boxed_2819_ = lean_unbox_usize(v_sz_2808_);
lean_dec(v_sz_2808_);
v_i_boxed_2820_ = lean_unbox_usize(v_i_2809_);
lean_dec(v_i_2809_);
v_res_2821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__1(v_as_2807_, v_sz_boxed_2819_, v_i_boxed_2820_, v_b_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v_as_2807_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement(lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v___x_2830_; lean_object* v_sorts_2831_; lean_object* v_buckets_2832_; lean_object* v___x_2833_; size_t v_sz_2834_; size_t v___x_2835_; lean_object* v___x_2836_; 
v___x_2830_ = lean_st_ref_get(v_a_2822_);
v_sorts_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc_ref(v_sorts_2831_);
lean_dec(v___x_2830_);
v_buckets_2832_ = lean_ctor_get(v_sorts_2831_, 1);
lean_inc_ref(v_buckets_2832_);
lean_dec_ref(v_sorts_2831_);
v___x_2833_ = lean_box(0);
v_sz_2834_ = lean_array_size(v_buckets_2832_);
v___x_2835_ = ((size_t)0ULL);
v___x_2836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__1(v_buckets_2832_, v_sz_2834_, v___x_2835_, v___x_2833_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
lean_dec_ref(v_buckets_2832_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v___x_2836_, 0);
lean_dec(v_unused_2844_);
v___x_2838_ = v___x_2836_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_dec(v___x_2836_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v___x_2833_);
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2833_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
else
{
return v___x_2836_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement___boxed(lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement(v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__2___redArg(lean_object* v_a_2854_, lean_object* v_b_2855_, lean_object* v_x_2856_){
_start:
{
if (lean_obj_tag(v_x_2856_) == 0)
{
lean_dec(v_b_2855_);
lean_dec_ref(v_a_2854_);
return v_x_2856_;
}
else
{
lean_object* v_key_2857_; lean_object* v_value_2858_; lean_object* v_tail_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2871_; 
v_key_2857_ = lean_ctor_get(v_x_2856_, 0);
v_value_2858_ = lean_ctor_get(v_x_2856_, 1);
v_tail_2859_ = lean_ctor_get(v_x_2856_, 2);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_x_2856_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2861_ = v_x_2856_;
v_isShared_2862_ = v_isSharedCheck_2871_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_tail_2859_);
lean_inc(v_value_2858_);
lean_inc(v_key_2857_);
lean_dec(v_x_2856_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2871_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
uint8_t v___x_2863_; 
v___x_2863_ = lean_expr_eqv(v_key_2857_, v_a_2854_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2866_; 
v___x_2864_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__2___redArg(v_a_2854_, v_b_2855_, v_tail_2859_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 2, v___x_2864_);
v___x_2866_ = v___x_2861_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_key_2857_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_value_2858_);
lean_ctor_set(v_reuseFailAlloc_2867_, 2, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
else
{
lean_object* v___x_2869_; 
lean_dec(v_value_2858_);
lean_dec(v_key_2857_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 1, v_b_2855_);
lean_ctor_set(v___x_2861_, 0, v_a_2854_);
v___x_2869_ = v___x_2861_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2854_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_b_2855_);
lean_ctor_set(v_reuseFailAlloc_2870_, 2, v_tail_2859_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___redArg(lean_object* v_a_2872_, lean_object* v_x_2873_){
_start:
{
if (lean_obj_tag(v_x_2873_) == 0)
{
uint8_t v___x_2874_; 
v___x_2874_ = 0;
return v___x_2874_;
}
else
{
lean_object* v_key_2875_; lean_object* v_tail_2876_; uint8_t v___x_2877_; 
v_key_2875_ = lean_ctor_get(v_x_2873_, 0);
v_tail_2876_ = lean_ctor_get(v_x_2873_, 2);
v___x_2877_ = lean_expr_eqv(v_key_2875_, v_a_2872_);
if (v___x_2877_ == 0)
{
v_x_2873_ = v_tail_2876_;
goto _start;
}
else
{
return v___x_2877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___redArg___boxed(lean_object* v_a_2879_, lean_object* v_x_2880_){
_start:
{
uint8_t v_res_2881_; lean_object* v_r_2882_; 
v_res_2881_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___redArg(v_a_2879_, v_x_2880_);
lean_dec(v_x_2880_);
lean_dec_ref(v_a_2879_);
v_r_2882_ = lean_box(v_res_2881_);
return v_r_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2_spec__10___redArg(lean_object* v_x_2883_, lean_object* v_x_2884_){
_start:
{
if (lean_obj_tag(v_x_2884_) == 0)
{
return v_x_2883_;
}
else
{
lean_object* v_key_2885_; lean_object* v_value_2886_; lean_object* v_tail_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2910_; 
v_key_2885_ = lean_ctor_get(v_x_2884_, 0);
v_value_2886_ = lean_ctor_get(v_x_2884_, 1);
v_tail_2887_ = lean_ctor_get(v_x_2884_, 2);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_x_2884_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2889_ = v_x_2884_;
v_isShared_2890_ = v_isSharedCheck_2910_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_tail_2887_);
lean_inc(v_value_2886_);
lean_inc(v_key_2885_);
lean_dec(v_x_2884_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2910_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; uint64_t v___x_2892_; uint64_t v___x_2893_; uint64_t v___x_2894_; uint64_t v_fold_2895_; uint64_t v___x_2896_; uint64_t v___x_2897_; uint64_t v___x_2898_; size_t v___x_2899_; size_t v___x_2900_; size_t v___x_2901_; size_t v___x_2902_; size_t v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2891_ = lean_array_get_size(v_x_2883_);
v___x_2892_ = l_Lean_Expr_hash(v_key_2885_);
v___x_2893_ = 32ULL;
v___x_2894_ = lean_uint64_shift_right(v___x_2892_, v___x_2893_);
v_fold_2895_ = lean_uint64_xor(v___x_2892_, v___x_2894_);
v___x_2896_ = 16ULL;
v___x_2897_ = lean_uint64_shift_right(v_fold_2895_, v___x_2896_);
v___x_2898_ = lean_uint64_xor(v_fold_2895_, v___x_2897_);
v___x_2899_ = lean_uint64_to_usize(v___x_2898_);
v___x_2900_ = lean_usize_of_nat(v___x_2891_);
v___x_2901_ = ((size_t)1ULL);
v___x_2902_ = lean_usize_sub(v___x_2900_, v___x_2901_);
v___x_2903_ = lean_usize_land(v___x_2899_, v___x_2902_);
v___x_2904_ = lean_array_uget_borrowed(v_x_2883_, v___x_2903_);
lean_inc(v___x_2904_);
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 2, v___x_2904_);
v___x_2906_ = v___x_2889_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_key_2885_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_value_2886_);
lean_ctor_set(v_reuseFailAlloc_2909_, 2, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2907_; 
v___x_2907_ = lean_array_uset(v_x_2883_, v___x_2903_, v___x_2906_);
v_x_2883_ = v___x_2907_;
v_x_2884_ = v_tail_2887_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2911_, lean_object* v_source_2912_, lean_object* v_target_2913_){
_start:
{
lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = lean_array_get_size(v_source_2912_);
v___x_2915_ = lean_nat_dec_lt(v_i_2911_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_dec_ref(v_source_2912_);
lean_dec(v_i_2911_);
return v_target_2913_;
}
else
{
lean_object* v_es_2916_; lean_object* v___x_2917_; lean_object* v_source_2918_; lean_object* v_target_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_es_2916_ = lean_array_fget(v_source_2912_, v_i_2911_);
v___x_2917_ = lean_box(0);
v_source_2918_ = lean_array_fset(v_source_2912_, v_i_2911_, v___x_2917_);
v_target_2919_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2_spec__10___redArg(v_target_2913_, v_es_2916_);
v___x_2920_ = lean_unsigned_to_nat(1u);
v___x_2921_ = lean_nat_add(v_i_2911_, v___x_2920_);
lean_dec(v_i_2911_);
v_i_2911_ = v___x_2921_;
v_source_2912_ = v_source_2918_;
v_target_2913_ = v_target_2919_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1___redArg(lean_object* v_data_2923_){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v_nbuckets_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2924_ = lean_array_get_size(v_data_2923_);
v___x_2925_ = lean_unsigned_to_nat(2u);
v_nbuckets_2926_ = lean_nat_mul(v___x_2924_, v___x_2925_);
v___x_2927_ = lean_unsigned_to_nat(0u);
v___x_2928_ = lean_box(0);
v___x_2929_ = lean_mk_array(v_nbuckets_2926_, v___x_2928_);
v___x_2930_ = lean_array_propagate_mark(v_data_2923_, v___x_2929_);
v___x_2931_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2___redArg(v___x_2927_, v_data_2923_, v___x_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0___redArg(lean_object* v_m_2932_, lean_object* v_a_2933_, lean_object* v_b_2934_){
_start:
{
lean_object* v_size_2935_; lean_object* v_buckets_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2979_; 
v_size_2935_ = lean_ctor_get(v_m_2932_, 0);
v_buckets_2936_ = lean_ctor_get(v_m_2932_, 1);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_m_2932_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2938_ = v_m_2932_;
v_isShared_2939_ = v_isSharedCheck_2979_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_buckets_2936_);
lean_inc(v_size_2935_);
lean_dec(v_m_2932_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2979_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; uint64_t v___x_2941_; uint64_t v___x_2942_; uint64_t v___x_2943_; uint64_t v_fold_2944_; uint64_t v___x_2945_; uint64_t v___x_2946_; uint64_t v___x_2947_; size_t v___x_2948_; size_t v___x_2949_; size_t v___x_2950_; size_t v___x_2951_; size_t v___x_2952_; lean_object* v_bkt_2953_; uint8_t v___x_2954_; 
v___x_2940_ = lean_array_get_size(v_buckets_2936_);
v___x_2941_ = l_Lean_Expr_hash(v_a_2933_);
v___x_2942_ = 32ULL;
v___x_2943_ = lean_uint64_shift_right(v___x_2941_, v___x_2942_);
v_fold_2944_ = lean_uint64_xor(v___x_2941_, v___x_2943_);
v___x_2945_ = 16ULL;
v___x_2946_ = lean_uint64_shift_right(v_fold_2944_, v___x_2945_);
v___x_2947_ = lean_uint64_xor(v_fold_2944_, v___x_2946_);
v___x_2948_ = lean_uint64_to_usize(v___x_2947_);
v___x_2949_ = lean_usize_of_nat(v___x_2940_);
v___x_2950_ = ((size_t)1ULL);
v___x_2951_ = lean_usize_sub(v___x_2949_, v___x_2950_);
v___x_2952_ = lean_usize_land(v___x_2948_, v___x_2951_);
v_bkt_2953_ = lean_array_uget_borrowed(v_buckets_2936_, v___x_2952_);
v___x_2954_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___redArg(v_a_2933_, v_bkt_2953_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; lean_object* v_size_x27_2956_; lean_object* v___x_2957_; lean_object* v_buckets_x27_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v___x_2955_ = lean_unsigned_to_nat(1u);
v_size_x27_2956_ = lean_nat_add(v_size_2935_, v___x_2955_);
lean_dec(v_size_2935_);
lean_inc(v_bkt_2953_);
v___x_2957_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2957_, 0, v_a_2933_);
lean_ctor_set(v___x_2957_, 1, v_b_2934_);
lean_ctor_set(v___x_2957_, 2, v_bkt_2953_);
v_buckets_x27_2958_ = lean_array_uset(v_buckets_2936_, v___x_2952_, v___x_2957_);
v___x_2959_ = lean_unsigned_to_nat(4u);
v___x_2960_ = lean_nat_mul(v_size_x27_2956_, v___x_2959_);
v___x_2961_ = lean_unsigned_to_nat(3u);
v___x_2962_ = lean_nat_div(v___x_2960_, v___x_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_array_get_size(v_buckets_x27_2958_);
v___x_2964_ = lean_nat_dec_le(v___x_2962_, v___x_2963_);
lean_dec(v___x_2962_);
if (v___x_2964_ == 0)
{
lean_object* v_val_2965_; lean_object* v___x_2967_; 
v_val_2965_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1___redArg(v_buckets_x27_2958_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 1, v_val_2965_);
lean_ctor_set(v___x_2938_, 0, v_size_x27_2956_);
v___x_2967_ = v___x_2938_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_size_x27_2956_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_val_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
else
{
lean_object* v___x_2970_; 
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 1, v_buckets_x27_2958_);
lean_ctor_set(v___x_2938_, 0, v_size_x27_2956_);
v___x_2970_ = v___x_2938_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_size_x27_2956_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_buckets_x27_2958_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
else
{
lean_object* v___x_2972_; lean_object* v_buckets_x27_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2977_; 
lean_inc(v_bkt_2953_);
v___x_2972_ = lean_box(0);
v_buckets_x27_2973_ = lean_array_uset(v_buckets_2936_, v___x_2952_, v___x_2972_);
v___x_2974_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__2___redArg(v_a_2933_, v_b_2934_, v_bkt_2953_);
v___x_2975_ = lean_array_uset(v_buckets_x27_2973_, v___x_2952_, v___x_2974_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 1, v___x_2975_);
v___x_2977_ = v___x_2938_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_size_2935_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___redArg(lean_object* v_m_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v_buckets_2982_; lean_object* v___x_2983_; uint64_t v___x_2984_; uint64_t v___x_2985_; uint64_t v___x_2986_; uint64_t v_fold_2987_; uint64_t v___x_2988_; uint64_t v___x_2989_; uint64_t v___x_2990_; size_t v___x_2991_; size_t v___x_2992_; size_t v___x_2993_; size_t v___x_2994_; size_t v___x_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v_buckets_2982_ = lean_ctor_get(v_m_2980_, 1);
v___x_2983_ = lean_array_get_size(v_buckets_2982_);
v___x_2984_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_a_2981_);
v___x_2985_ = 32ULL;
v___x_2986_ = lean_uint64_shift_right(v___x_2984_, v___x_2985_);
v_fold_2987_ = lean_uint64_xor(v___x_2984_, v___x_2986_);
v___x_2988_ = 16ULL;
v___x_2989_ = lean_uint64_shift_right(v_fold_2987_, v___x_2988_);
v___x_2990_ = lean_uint64_xor(v_fold_2987_, v___x_2989_);
v___x_2991_ = lean_uint64_to_usize(v___x_2990_);
v___x_2992_ = lean_usize_of_nat(v___x_2983_);
v___x_2993_ = ((size_t)1ULL);
v___x_2994_ = lean_usize_sub(v___x_2992_, v___x_2993_);
v___x_2995_ = lean_usize_land(v___x_2991_, v___x_2994_);
v___x_2996_ = lean_array_uget_borrowed(v_buckets_2982_, v___x_2995_);
v___x_2997_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___redArg(v_a_2981_, v___x_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___redArg___boxed(lean_object* v_m_2998_, lean_object* v_a_2999_){
_start:
{
uint8_t v_res_3000_; lean_object* v_r_3001_; 
v_res_3000_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___redArg(v_m_2998_, v_a_2999_);
lean_dec(v_a_2999_);
lean_dec_ref(v_m_2998_);
v_r_3001_ = lean_box(v_res_3000_);
return v_r_3001_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__2(lean_object* v___x_3002_, lean_object* v_as_3003_, size_t v_i_3004_, size_t v_stop_3005_){
_start:
{
uint8_t v___x_3006_; 
v___x_3006_ = lean_usize_dec_eq(v_i_3004_, v_stop_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3007_ = lean_array_uget_borrowed(v_as_3003_, v_i_3004_);
v___x_3008_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___redArg(v___x_3002_, v___x_3007_);
if (v___x_3008_ == 0)
{
uint8_t v___x_3009_; 
v___x_3009_ = 1;
return v___x_3009_;
}
else
{
size_t v___x_3010_; size_t v___x_3011_; 
v___x_3010_ = ((size_t)1ULL);
v___x_3011_ = lean_usize_add(v_i_3004_, v___x_3010_);
v_i_3004_ = v___x_3011_;
goto _start;
}
}
else
{
uint8_t v___x_3013_; 
v___x_3013_ = 0;
return v___x_3013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__2___boxed(lean_object* v___x_3014_, lean_object* v_as_3015_, lean_object* v_i_3016_, lean_object* v_stop_3017_){
_start:
{
size_t v_i_boxed_3018_; size_t v_stop_boxed_3019_; uint8_t v_res_3020_; lean_object* v_r_3021_; 
v_i_boxed_3018_ = lean_unbox_usize(v_i_3016_);
lean_dec(v_i_3016_);
v_stop_boxed_3019_ = lean_unbox_usize(v_stop_3017_);
lean_dec(v_stop_3017_);
v_res_3020_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__2(v___x_3014_, v_as_3015_, v_i_boxed_3018_, v_stop_boxed_3019_);
lean_dec_ref(v_as_3015_);
lean_dec_ref(v___x_3014_);
v_r_3021_ = lean_box(v_res_3020_);
return v_r_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___redArg(lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
if (lean_obj_tag(v_a_3022_) == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_a_3023_);
v___x_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
return v___x_3026_;
}
else
{
lean_object* v_value_3027_; lean_object* v_key_3028_; lean_object* v_tail_3029_; lean_object* v_argumentSorts_3030_; lean_object* v_sortInfo_3031_; lean_object* v_sortMap_3032_; lean_object* v_predInfo_3033_; lean_object* v_groundFacts_3034_; lean_object* v_quantifiedFacts_3035_; lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v_value_3027_ = lean_ctor_get(v_a_3022_, 1);
lean_inc(v_value_3027_);
v_key_3028_ = lean_ctor_get(v_a_3022_, 0);
lean_inc(v_key_3028_);
v_tail_3029_ = lean_ctor_get(v_a_3022_, 2);
lean_inc(v_tail_3029_);
lean_dec_ref_known(v_a_3022_, 3);
v_argumentSorts_3030_ = lean_ctor_get(v_value_3027_, 0);
v_sortInfo_3031_ = lean_ctor_get(v_a_3023_, 0);
v_sortMap_3032_ = lean_ctor_get(v_a_3023_, 1);
v_predInfo_3033_ = lean_ctor_get(v_a_3023_, 2);
v_groundFacts_3034_ = lean_ctor_get(v_a_3023_, 3);
v_quantifiedFacts_3035_ = lean_ctor_get(v_a_3023_, 4);
v___x_3040_ = lean_unsigned_to_nat(0u);
v___x_3041_ = lean_array_get_size(v_argumentSorts_3030_);
v___x_3042_ = lean_nat_dec_lt(v___x_3040_, v___x_3041_);
if (v___x_3042_ == 0)
{
lean_inc_ref(v_quantifiedFacts_3035_);
lean_inc_ref(v_groundFacts_3034_);
lean_inc_ref(v_predInfo_3033_);
lean_inc_ref(v_sortMap_3032_);
lean_inc_ref(v_sortInfo_3031_);
lean_dec_ref(v_a_3023_);
goto v___jp_3036_;
}
else
{
if (v___x_3042_ == 0)
{
lean_inc_ref(v_quantifiedFacts_3035_);
lean_inc_ref(v_groundFacts_3034_);
lean_inc_ref(v_predInfo_3033_);
lean_inc_ref(v_sortMap_3032_);
lean_inc_ref(v_sortInfo_3031_);
lean_dec_ref(v_a_3023_);
goto v___jp_3036_;
}
else
{
size_t v___x_3043_; size_t v___x_3044_; uint8_t v___x_3045_; 
v___x_3043_ = ((size_t)0ULL);
v___x_3044_ = lean_usize_of_nat(v___x_3041_);
v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__2(v_sortInfo_3031_, v_argumentSorts_3030_, v___x_3043_, v___x_3044_);
if (v___x_3045_ == 0)
{
lean_inc_ref(v_quantifiedFacts_3035_);
lean_inc_ref(v_groundFacts_3034_);
lean_inc_ref(v_predInfo_3033_);
lean_inc_ref(v_sortMap_3032_);
lean_inc_ref(v_sortInfo_3031_);
lean_dec_ref(v_a_3023_);
goto v___jp_3036_;
}
else
{
lean_dec(v_key_3028_);
lean_dec(v_value_3027_);
v_a_3022_ = v_tail_3029_;
goto _start;
}
}
}
v___jp_3036_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0___redArg(v_predInfo_3033_, v_key_3028_, v_value_3027_);
v___x_3038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3038_, 0, v_sortInfo_3031_);
lean_ctor_set(v___x_3038_, 1, v_sortMap_3032_);
lean_ctor_set(v___x_3038_, 2, v___x_3037_);
lean_ctor_set(v___x_3038_, 3, v_groundFacts_3034_);
lean_ctor_set(v___x_3038_, 4, v_quantifiedFacts_3035_);
v_a_3022_ = v_tail_3029_;
v_a_3023_ = v___x_3038_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___redArg___boxed(lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___redArg(v_a_3047_, v_a_3048_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__7(lean_object* v_as_3051_, size_t v_sz_3052_, size_t v_i_3053_, lean_object* v_b_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
uint8_t v___x_3063_; 
v___x_3063_ = lean_usize_dec_lt(v_i_3053_, v_sz_3052_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; 
v___x_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3064_, 0, v_b_3054_);
return v___x_3064_;
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3066_; 
v_a_3065_ = lean_array_uget_borrowed(v_as_3051_, v_i_3053_);
lean_inc(v_a_3065_);
v___x_3066_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___redArg(v_a_3065_, v_b_3054_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3079_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3079_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3079_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
if (lean_obj_tag(v_a_3067_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3073_; 
v_a_3071_ = lean_ctor_get(v_a_3067_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v_a_3067_, 1);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v_a_3071_);
v___x_3073_ = v___x_3069_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
else
{
lean_object* v_a_3075_; size_t v___x_3076_; size_t v___x_3077_; 
lean_del_object(v___x_3069_);
v_a_3075_ = lean_ctor_get(v_a_3067_, 0);
lean_inc(v_a_3075_);
lean_dec_ref_known(v_a_3067_, 1);
v___x_3076_ = ((size_t)1ULL);
v___x_3077_ = lean_usize_add(v_i_3053_, v___x_3076_);
v_i_3053_ = v___x_3077_;
v_b_3054_ = v_a_3075_;
goto _start;
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
v_a_3080_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3066_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3066_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__7___boxed(lean_object* v_as_3088_, lean_object* v_sz_3089_, lean_object* v_i_3090_, lean_object* v_b_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
size_t v_sz_boxed_3100_; size_t v_i_boxed_3101_; lean_object* v_res_3102_; 
v_sz_boxed_3100_ = lean_unbox_usize(v_sz_3089_);
lean_dec(v_sz_3089_);
v_i_boxed_3101_ = lean_unbox_usize(v_i_3090_);
lean_dec(v_i_3090_);
v_res_3102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__7(v_as_3088_, v_sz_boxed_3100_, v_i_boxed_3101_, v_b_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v_as_3088_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__4(lean_object* v_a_3103_, lean_object* v_as_3104_, size_t v_i_3105_, size_t v_stop_3106_, lean_object* v_b_3107_){
_start:
{
uint8_t v___x_3108_; 
v___x_3108_ = lean_usize_dec_eq(v_i_3105_, v_stop_3106_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3110_; size_t v___x_3111_; size_t v___x_3112_; 
v___x_3109_ = lean_array_uget_borrowed(v_as_3104_, v_i_3105_);
lean_inc(v_a_3103_);
lean_inc(v___x_3109_);
v___x_3110_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0___redArg(v_b_3107_, v___x_3109_, v_a_3103_);
v___x_3111_ = ((size_t)1ULL);
v___x_3112_ = lean_usize_add(v_i_3105_, v___x_3111_);
v_i_3105_ = v___x_3112_;
v_b_3107_ = v___x_3110_;
goto _start;
}
else
{
lean_dec(v_a_3103_);
return v_b_3107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__4___boxed(lean_object* v_a_3114_, lean_object* v_as_3115_, lean_object* v_i_3116_, lean_object* v_stop_3117_, lean_object* v_b_3118_){
_start:
{
size_t v_i_boxed_3119_; size_t v_stop_boxed_3120_; lean_object* v_res_3121_; 
v_i_boxed_3119_ = lean_unbox_usize(v_i_3116_);
lean_dec(v_i_3116_);
v_stop_boxed_3120_ = lean_unbox_usize(v_stop_3117_);
lean_dec(v_stop_3117_);
v_res_3121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__4(v_a_3114_, v_as_3115_, v_i_boxed_3119_, v_stop_boxed_3120_, v_b_3118_);
lean_dec_ref(v_as_3115_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___redArg(lean_object* v_a_3122_, lean_object* v_a_3123_){
_start:
{
if (lean_obj_tag(v_a_3122_) == 0)
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3125_, 0, v_a_3123_);
v___x_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
return v___x_3126_;
}
else
{
lean_object* v_value_3127_; lean_object* v_key_3128_; lean_object* v_tail_3129_; lean_object* v_type_3130_; lean_object* v_level_3131_; lean_object* v_elements_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3163_; 
v_value_3127_ = lean_ctor_get(v_a_3122_, 1);
lean_inc(v_value_3127_);
v_key_3128_ = lean_ctor_get(v_a_3122_, 0);
lean_inc(v_key_3128_);
v_tail_3129_ = lean_ctor_get(v_a_3122_, 2);
lean_inc(v_tail_3129_);
lean_dec_ref_known(v_a_3122_, 3);
v_type_3130_ = lean_ctor_get(v_value_3127_, 0);
v_level_3131_ = lean_ctor_get(v_value_3127_, 1);
v_elements_3132_ = lean_ctor_get(v_value_3127_, 2);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_value_3127_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3134_ = v_value_3127_;
v_isShared_3135_ = v_isSharedCheck_3163_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_elements_3132_);
lean_inc(v_level_3131_);
lean_inc(v_type_3130_);
lean_dec(v_value_3127_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3163_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; 
v___x_3136_ = lean_array_get_size(v_elements_3132_);
v___x_3137_ = lean_unsigned_to_nat(0u);
v___x_3138_ = lean_nat_dec_eq(v___x_3136_, v___x_3137_);
if (v___x_3138_ == 0)
{
lean_object* v_sortInfo_3139_; lean_object* v_sortMap_3140_; lean_object* v_predInfo_3141_; lean_object* v_groundFacts_3142_; lean_object* v_quantifiedFacts_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3161_; 
v_sortInfo_3139_ = lean_ctor_get(v_a_3123_, 0);
v_sortMap_3140_ = lean_ctor_get(v_a_3123_, 1);
v_predInfo_3141_ = lean_ctor_get(v_a_3123_, 2);
v_groundFacts_3142_ = lean_ctor_get(v_a_3123_, 3);
v_quantifiedFacts_3143_ = lean_ctor_get(v_a_3123_, 4);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_a_3123_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3145_ = v_a_3123_;
v_isShared_3146_ = v_isSharedCheck_3161_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_quantifiedFacts_3143_);
lean_inc(v_groundFacts_3142_);
lean_inc(v_predInfo_3141_);
lean_inc(v_sortMap_3140_);
lean_inc(v_sortInfo_3139_);
lean_dec(v_a_3123_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3161_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
lean_inc_ref(v_elements_3132_);
if (v_isShared_3135_ == 0)
{
v___x_3148_ = v___x_3134_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_type_3130_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_level_3131_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v_elements_3132_);
v___x_3148_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3149_; lean_object* v___y_3151_; uint8_t v___x_3156_; 
lean_inc(v_key_3128_);
v___x_3149_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0___redArg(v_sortInfo_3139_, v_key_3128_, v___x_3148_);
v___x_3156_ = lean_nat_dec_lt(v___x_3137_, v___x_3136_);
if (v___x_3156_ == 0)
{
lean_dec_ref(v_elements_3132_);
lean_dec(v_key_3128_);
v___y_3151_ = v_sortMap_3140_;
goto v___jp_3150_;
}
else
{
size_t v___x_3157_; size_t v___x_3158_; lean_object* v___x_3159_; 
v___x_3157_ = ((size_t)0ULL);
v___x_3158_ = lean_usize_of_nat(v___x_3136_);
v___x_3159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__4(v_key_3128_, v_elements_3132_, v___x_3157_, v___x_3158_, v_sortMap_3140_);
lean_dec_ref(v_elements_3132_);
v___y_3151_ = v___x_3159_;
goto v___jp_3150_;
}
v___jp_3150_:
{
lean_object* v___x_3153_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 1, v___y_3151_);
lean_ctor_set(v___x_3145_, 0, v___x_3149_);
v___x_3153_ = v___x_3145_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3149_);
lean_ctor_set(v_reuseFailAlloc_3155_, 1, v___y_3151_);
lean_ctor_set(v_reuseFailAlloc_3155_, 2, v_predInfo_3141_);
lean_ctor_set(v_reuseFailAlloc_3155_, 3, v_groundFacts_3142_);
lean_ctor_set(v_reuseFailAlloc_3155_, 4, v_quantifiedFacts_3143_);
v___x_3153_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
v_a_3122_ = v_tail_3129_;
v_a_3123_ = v___x_3153_;
goto _start;
}
}
}
}
}
else
{
lean_del_object(v___x_3134_);
lean_dec_ref(v_elements_3132_);
lean_dec(v_level_3131_);
lean_dec_ref(v_type_3130_);
lean_dec(v_key_3128_);
v_a_3122_ = v_tail_3129_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___redArg___boxed(lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___redArg(v_a_3164_, v_a_3165_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__6(lean_object* v_as_3168_, size_t v_sz_3169_, size_t v_i_3170_, lean_object* v_b_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
uint8_t v___x_3180_; 
v___x_3180_ = lean_usize_dec_lt(v_i_3170_, v_sz_3169_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; 
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v_b_3171_);
return v___x_3181_;
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3183_; 
v_a_3182_ = lean_array_uget_borrowed(v_as_3168_, v_i_3170_);
lean_inc(v_a_3182_);
v___x_3183_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___redArg(v_a_3182_, v_b_3171_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3196_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3186_ = v___x_3183_;
v_isShared_3187_ = v_isSharedCheck_3196_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3183_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3196_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
if (lean_obj_tag(v_a_3184_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3190_; 
v_a_3188_ = lean_ctor_get(v_a_3184_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v_a_3184_, 1);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 0, v_a_3188_);
v___x_3190_ = v___x_3186_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3188_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
else
{
lean_object* v_a_3192_; size_t v___x_3193_; size_t v___x_3194_; 
lean_del_object(v___x_3186_);
v_a_3192_ = lean_ctor_get(v_a_3184_, 0);
lean_inc(v_a_3192_);
lean_dec_ref_known(v_a_3184_, 1);
v___x_3193_ = ((size_t)1ULL);
v___x_3194_ = lean_usize_add(v_i_3170_, v___x_3193_);
v_i_3170_ = v___x_3194_;
v_b_3171_ = v_a_3192_;
goto _start;
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
v_a_3197_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3183_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3183_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__6___boxed(lean_object* v_as_3205_, lean_object* v_sz_3206_, lean_object* v_i_3207_, lean_object* v_b_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
size_t v_sz_boxed_3217_; size_t v_i_boxed_3218_; lean_object* v_res_3219_; 
v_sz_boxed_3217_ = lean_unbox_usize(v_sz_3206_);
lean_dec(v_sz_3206_);
v_i_boxed_3218_ = lean_unbox_usize(v_i_3207_);
lean_dec(v_i_3207_);
v_res_3219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__6(v_as_3205_, v_sz_boxed_3217_, v_i_boxed_3218_, v_b_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v_as_3205_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble(lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v_sorts_3230_; lean_object* v_preds_3231_; lean_object* v_groundFacts_3232_; lean_object* v_quantifiedFacts_3233_; lean_object* v_remainingHyps_3234_; lean_object* v_buckets_3235_; lean_object* v___x_3236_; size_t v_sz_3237_; size_t v___x_3238_; lean_object* v___x_3239_; 
v___x_3228_ = lean_st_ref_get(v_a_3220_);
v___x_3229_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__1);
v_sorts_3230_ = lean_ctor_get(v___x_3228_, 0);
lean_inc_ref(v_sorts_3230_);
v_preds_3231_ = lean_ctor_get(v___x_3228_, 4);
lean_inc_ref(v_preds_3231_);
v_groundFacts_3232_ = lean_ctor_get(v___x_3228_, 5);
lean_inc_ref(v_groundFacts_3232_);
v_quantifiedFacts_3233_ = lean_ctor_get(v___x_3228_, 6);
lean_inc_ref(v_quantifiedFacts_3233_);
v_remainingHyps_3234_ = lean_ctor_get(v___x_3228_, 7);
lean_inc_ref(v_remainingHyps_3234_);
lean_dec(v___x_3228_);
v_buckets_3235_ = lean_ctor_get(v_sorts_3230_, 1);
lean_inc_ref(v_buckets_3235_);
lean_dec_ref(v_sorts_3230_);
v___x_3236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3229_);
lean_ctor_set(v___x_3236_, 1, v___x_3229_);
lean_ctor_set(v___x_3236_, 2, v___x_3229_);
lean_ctor_set(v___x_3236_, 3, v_groundFacts_3232_);
lean_ctor_set(v___x_3236_, 4, v_quantifiedFacts_3233_);
v_sz_3237_ = lean_array_size(v_buckets_3235_);
v___x_3238_ = ((size_t)0ULL);
v___x_3239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__6(v_buckets_3235_, v_sz_3237_, v___x_3238_, v___x_3236_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
lean_dec_ref(v_buckets_3235_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v_buckets_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3266_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref_known(v___x_3239_, 1);
v_buckets_3241_ = lean_ctor_get(v_preds_3231_, 1);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_preds_3231_);
if (v_isSharedCheck_3266_ == 0)
{
lean_object* v_unused_3267_; 
v_unused_3267_ = lean_ctor_get(v_preds_3231_, 0);
lean_dec(v_unused_3267_);
v___x_3243_ = v_preds_3231_;
v_isShared_3244_ = v_isSharedCheck_3266_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_buckets_3241_);
lean_dec(v_preds_3231_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3266_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
size_t v_sz_3245_; lean_object* v___x_3246_; 
v_sz_3245_ = lean_array_size(v_buckets_3241_);
v___x_3246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__7(v_buckets_3241_, v_sz_3245_, v___x_3238_, v_a_3240_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
lean_dec_ref(v_buckets_3241_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3257_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3249_ = v___x_3246_;
v_isShared_3250_ = v_isSharedCheck_3257_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3257_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 1, v_remainingHyps_3234_);
lean_ctor_set(v___x_3243_, 0, v_a_3247_);
v___x_3252_ = v___x_3243_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3247_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_remainingHyps_3234_);
v___x_3252_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3254_; 
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3252_);
v___x_3254_ = v___x_3249_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_del_object(v___x_3243_);
lean_dec_ref(v_remainingHyps_3234_);
v_a_3258_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3246_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3246_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_dec_ref(v_remainingHyps_3234_);
lean_dec_ref(v_preds_3231_);
v_a_3268_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3239_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3239_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble___boxed(lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble(v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3277_);
lean_dec(v_a_3276_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0(lean_object* v_00_u03b2_3285_, lean_object* v_m_3286_, lean_object* v_a_3287_, lean_object* v_b_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0___redArg(v_m_3286_, v_a_3287_, v_b_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1(lean_object* v_00_u03b2_3290_, lean_object* v_m_3291_, lean_object* v_a_3292_){
_start:
{
uint8_t v___x_3293_; 
v___x_3293_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___redArg(v_m_3291_, v_a_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___boxed(lean_object* v_00_u03b2_3294_, lean_object* v_m_3295_, lean_object* v_a_3296_){
_start:
{
uint8_t v_res_3297_; lean_object* v_r_3298_; 
v_res_3297_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1(v_00_u03b2_3294_, v_m_3295_, v_a_3296_);
lean_dec(v_a_3296_);
lean_dec_ref(v_m_3295_);
v_r_3298_ = lean_box(v_res_3297_);
return v_r_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3(lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___redArg(v_a_3299_, v_a_3300_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___boxed(lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3(v_a_3310_, v_a_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5(lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___redArg(v_a_3321_, v_a_3322_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___boxed(lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5(v_a_3332_, v_a_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
return v_res_3342_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0(lean_object* v_00_u03b2_3343_, lean_object* v_a_3344_, lean_object* v_x_3345_){
_start:
{
uint8_t v___x_3346_; 
v___x_3346_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___redArg(v_a_3344_, v_x_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3347_, lean_object* v_a_3348_, lean_object* v_x_3349_){
_start:
{
uint8_t v_res_3350_; lean_object* v_r_3351_; 
v_res_3350_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0(v_00_u03b2_3347_, v_a_3348_, v_x_3349_);
lean_dec(v_x_3349_);
lean_dec_ref(v_a_3348_);
v_r_3351_ = lean_box(v_res_3350_);
return v_r_3351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1(lean_object* v_00_u03b2_3352_, lean_object* v_data_3353_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1___redArg(v_data_3353_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__2(lean_object* v_00_u03b2_3355_, lean_object* v_a_3356_, lean_object* v_b_3357_, lean_object* v_x_3358_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__2___redArg(v_a_3356_, v_b_3357_, v_x_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3360_, lean_object* v_i_3361_, lean_object* v_source_3362_, lean_object* v_target_3363_){
_start:
{
lean_object* v___x_3364_; 
v___x_3364_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2___redArg(v_i_3361_, v_source_3362_, v_target_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2_spec__10(lean_object* v_00_u03b2_3365_, lean_object* v_x_3366_, lean_object* v_x_3367_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2_spec__10___redArg(v_x_3366_, v_x_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2_spec__6(lean_object* v_as_3369_, size_t v_i_3370_, size_t v_stop_3371_, lean_object* v_b_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_a_3382_; uint8_t v___x_3386_; 
v___x_3386_ = lean_usize_dec_eq(v_i_3370_, v_stop_3371_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; 
v___x_3387_ = lean_array_uget_borrowed(v_as_3369_, v_i_3370_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v___x_3388_; 
v___x_3388_ = lean_box(0);
v_a_3382_ = v___x_3388_;
goto v___jp_3381_;
}
else
{
lean_object* v_val_3389_; lean_object* v___x_3390_; 
v_val_3389_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_val_3389_);
v___x_3390_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processLocalDecl(v_val_3389_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3390_, 1);
v_a_3382_ = v_a_3391_;
goto v___jp_3381_;
}
else
{
return v___x_3390_;
}
}
}
else
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v_b_3372_);
return v___x_3392_;
}
v___jp_3381_:
{
size_t v___x_3383_; size_t v___x_3384_; 
v___x_3383_ = ((size_t)1ULL);
v___x_3384_ = lean_usize_add(v_i_3370_, v___x_3383_);
v_i_3370_ = v___x_3384_;
v_b_3372_ = v_a_3382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_as_3393_, lean_object* v_i_3394_, lean_object* v_stop_3395_, lean_object* v_b_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
size_t v_i_boxed_3405_; size_t v_stop_boxed_3406_; lean_object* v_res_3407_; 
v_i_boxed_3405_ = lean_unbox_usize(v_i_3394_);
lean_dec(v_i_3394_);
v_stop_boxed_3406_ = lean_unbox_usize(v_stop_3395_);
lean_dec(v_stop_3395_);
v_res_3407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2_spec__6(v_as_3393_, v_i_boxed_3405_, v_stop_boxed_3406_, v_b_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v_as_3393_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(lean_object* v_as_3408_, size_t v_i_3409_, size_t v_stop_3410_, lean_object* v_b_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_a_3421_; uint8_t v___x_3425_; 
v___x_3425_ = lean_usize_dec_eq(v_i_3409_, v_stop_3410_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_array_uget_borrowed(v_as_3408_, v_i_3409_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_box(0);
v_a_3421_ = v___x_3427_;
goto v___jp_3420_;
}
else
{
lean_object* v_val_3428_; lean_object* v___x_3429_; 
v_val_3428_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_val_3428_);
v___x_3429_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processLocalDecl(v_val_3428_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3429_, 1);
v_a_3421_ = v_a_3430_;
goto v___jp_3420_;
}
else
{
return v___x_3429_;
}
}
}
else
{
lean_object* v___x_3431_; 
v___x_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3431_, 0, v_b_3411_);
return v___x_3431_;
}
v___jp_3420_:
{
size_t v___x_3422_; size_t v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = ((size_t)1ULL);
v___x_3423_ = lean_usize_add(v_i_3409_, v___x_3422_);
v___x_3424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2_spec__6(v_as_3408_, v___x_3423_, v_stop_3410_, v_a_3421_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
return v___x_3424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3432_, lean_object* v_i_3433_, lean_object* v_stop_3434_, lean_object* v_b_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
size_t v_i_boxed_3444_; size_t v_stop_boxed_3445_; lean_object* v_res_3446_; 
v_i_boxed_3444_ = lean_unbox_usize(v_i_3433_);
lean_dec(v_i_3433_);
v_stop_boxed_3445_ = lean_unbox_usize(v_stop_3434_);
lean_dec(v_stop_3434_);
v_res_3446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(v_as_3432_, v_i_boxed_3444_, v_stop_boxed_3445_, v_b_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v_as_3432_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
if (lean_obj_tag(v_x_3447_) == 0)
{
lean_object* v_cs_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3470_; 
v_cs_3456_ = lean_ctor_get(v_x_3447_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_x_3447_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3458_ = v_x_3447_;
v_isShared_3459_ = v_isSharedCheck_3470_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_cs_3456_);
lean_dec(v_x_3447_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3470_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; uint8_t v___x_3463_; 
v___x_3460_ = lean_unsigned_to_nat(0u);
v___x_3461_ = lean_array_get_size(v_cs_3456_);
v___x_3462_ = lean_box(0);
v___x_3463_ = lean_nat_dec_lt(v___x_3460_, v___x_3461_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3465_; 
lean_dec_ref(v_cs_3456_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v___x_3462_);
v___x_3465_ = v___x_3458_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3462_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
else
{
size_t v___x_3467_; size_t v___x_3468_; lean_object* v___x_3469_; 
lean_del_object(v___x_3458_);
v___x_3467_ = ((size_t)0ULL);
v___x_3468_ = lean_usize_of_nat(v___x_3461_);
v___x_3469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__4(v_cs_3456_, v___x_3467_, v___x_3468_, v___x_3462_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec_ref(v_cs_3456_);
return v___x_3469_;
}
}
}
else
{
lean_object* v_vs_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3485_; 
v_vs_3471_ = lean_ctor_get(v_x_3447_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v_x_3447_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3473_ = v_x_3447_;
v_isShared_3474_ = v_isSharedCheck_3485_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_vs_3471_);
lean_dec(v_x_3447_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3485_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; uint8_t v___x_3478_; 
v___x_3475_ = lean_unsigned_to_nat(0u);
v___x_3476_ = lean_array_get_size(v_vs_3471_);
v___x_3477_ = lean_box(0);
v___x_3478_ = lean_nat_dec_lt(v___x_3475_, v___x_3476_);
if (v___x_3478_ == 0)
{
lean_object* v___x_3480_; 
lean_dec_ref(v_vs_3471_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set_tag(v___x_3473_, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3477_);
v___x_3480_ = v___x_3473_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3477_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
else
{
size_t v___x_3482_; size_t v___x_3483_; lean_object* v___x_3484_; 
lean_del_object(v___x_3473_);
v___x_3482_ = ((size_t)0ULL);
v___x_3483_ = lean_usize_of_nat(v___x_3476_);
v___x_3484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(v_vs_3471_, v___x_3482_, v___x_3483_, v___x_3477_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec_ref(v_vs_3471_);
return v___x_3484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__4(lean_object* v_as_3486_, size_t v_i_3487_, size_t v_stop_3488_, lean_object* v_b_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
uint8_t v___x_3498_; 
v___x_3498_ = lean_usize_dec_eq(v_i_3487_, v_stop_3488_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = lean_array_uget_borrowed(v_as_3486_, v_i_3487_);
lean_inc(v___x_3499_);
v___x_3500_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__3(v___x_3499_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; size_t v___x_3502_; size_t v___x_3503_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___x_3502_ = ((size_t)1ULL);
v___x_3503_ = lean_usize_add(v_i_3487_, v___x_3502_);
v_i_3487_ = v___x_3503_;
v_b_3489_ = v_a_3501_;
goto _start;
}
else
{
return v___x_3500_;
}
}
else
{
lean_object* v___x_3505_; 
v___x_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3505_, 0, v_b_3489_);
return v___x_3505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3506_, lean_object* v_i_3507_, lean_object* v_stop_3508_, lean_object* v_b_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
size_t v_i_boxed_3518_; size_t v_stop_boxed_3519_; lean_object* v_res_3520_; 
v_i_boxed_3518_ = lean_unbox_usize(v_i_3507_);
lean_dec(v_i_3507_);
v_stop_boxed_3519_ = lean_unbox_usize(v_stop_3508_);
lean_dec(v_stop_3508_);
v_res_3520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__4(v_as_3506_, v_i_boxed_3518_, v_stop_boxed_3519_, v_b_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v_as_3506_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__3(v_x_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec(v___y_3522_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__3(lean_object* v_t_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_root_3540_; lean_object* v_tail_3541_; lean_object* v___x_3542_; 
v_root_3540_ = lean_ctor_get(v_t_3531_, 0);
lean_inc_ref(v_root_3540_);
v_tail_3541_ = lean_ctor_get(v_t_3531_, 1);
lean_inc_ref(v_tail_3541_);
lean_dec_ref(v_t_3531_);
v___x_3542_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__3(v_root_3540_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3556_; 
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3556_ == 0)
{
lean_object* v_unused_3557_; 
v_unused_3557_ = lean_ctor_get(v___x_3542_, 0);
lean_dec(v_unused_3557_);
v___x_3544_ = v___x_3542_;
v_isShared_3545_ = v_isSharedCheck_3556_;
goto v_resetjp_3543_;
}
else
{
lean_dec(v___x_3542_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3556_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v___x_3546_ = lean_unsigned_to_nat(0u);
v___x_3547_ = lean_array_get_size(v_tail_3541_);
v___x_3548_ = lean_box(0);
v___x_3549_ = lean_nat_dec_lt(v___x_3546_, v___x_3547_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3551_; 
lean_dec_ref(v_tail_3541_);
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 0, v___x_3548_);
v___x_3551_ = v___x_3544_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3548_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
else
{
size_t v___x_3553_; size_t v___x_3554_; lean_object* v___x_3555_; 
lean_del_object(v___x_3544_);
v___x_3553_ = ((size_t)0ULL);
v___x_3554_ = lean_usize_of_nat(v___x_3547_);
v___x_3555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(v_tail_3541_, v___x_3553_, v___x_3554_, v___x_3548_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec_ref(v_tail_3541_);
return v___x_3555_;
}
}
}
else
{
lean_dec_ref(v_tail_3541_);
return v___x_3542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__3___boxed(lean_object* v_t_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__3(v_t_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
return v_res_3567_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3568_; 
v___x_3568_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1(lean_object* v_x_3569_, size_t v_x_3570_, size_t v_x_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
if (lean_obj_tag(v_x_3569_) == 0)
{
lean_object* v_cs_3580_; lean_object* v___x_3581_; size_t v___x_3582_; lean_object* v_j_3583_; lean_object* v___x_3584_; size_t v___x_3585_; size_t v___x_3586_; size_t v___x_3587_; size_t v___x_3588_; size_t v___x_3589_; size_t v___x_3590_; lean_object* v___x_3591_; 
v_cs_3580_ = lean_ctor_get(v_x_3569_, 0);
lean_inc_ref(v_cs_3580_);
lean_dec_ref_known(v_x_3569_, 1);
v___x_3581_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1___closed__0);
v___x_3582_ = lean_usize_shift_right(v_x_3570_, v_x_3571_);
v_j_3583_ = lean_usize_to_nat(v___x_3582_);
v___x_3584_ = lean_array_get_borrowed(v___x_3581_, v_cs_3580_, v_j_3583_);
v___x_3585_ = ((size_t)1ULL);
v___x_3586_ = lean_usize_shift_left(v___x_3585_, v_x_3571_);
v___x_3587_ = lean_usize_sub(v___x_3586_, v___x_3585_);
v___x_3588_ = lean_usize_land(v_x_3570_, v___x_3587_);
v___x_3589_ = ((size_t)5ULL);
v___x_3590_ = lean_usize_sub(v_x_3571_, v___x_3589_);
lean_inc(v___x_3584_);
v___x_3591_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1(v___x_3584_, v___x_3588_, v___x_3590_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3606_; 
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; 
v_unused_3607_ = lean_ctor_get(v___x_3591_, 0);
lean_dec(v_unused_3607_);
v___x_3593_ = v___x_3591_;
v_isShared_3594_ = v_isSharedCheck_3606_;
goto v_resetjp_3592_;
}
else
{
lean_dec(v___x_3591_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3606_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v___x_3595_ = lean_unsigned_to_nat(1u);
v___x_3596_ = lean_nat_add(v_j_3583_, v___x_3595_);
lean_dec(v_j_3583_);
v___x_3597_ = lean_array_get_size(v_cs_3580_);
v___x_3598_ = lean_box(0);
v___x_3599_ = lean_nat_dec_lt(v___x_3596_, v___x_3597_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3601_; 
lean_dec(v___x_3596_);
lean_dec_ref(v_cs_3580_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v___x_3598_);
v___x_3601_ = v___x_3593_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3598_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
else
{
size_t v___x_3603_; size_t v___x_3604_; lean_object* v___x_3605_; 
lean_del_object(v___x_3593_);
v___x_3603_ = lean_usize_of_nat(v___x_3596_);
lean_dec(v___x_3596_);
v___x_3604_ = lean_usize_of_nat(v___x_3597_);
v___x_3605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__4(v_cs_3580_, v___x_3603_, v___x_3604_, v___x_3598_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec_ref(v_cs_3580_);
return v___x_3605_;
}
}
}
else
{
lean_dec(v_j_3583_);
lean_dec_ref(v_cs_3580_);
return v___x_3591_;
}
}
else
{
lean_object* v_vs_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3622_; 
v_vs_3608_ = lean_ctor_get(v_x_3569_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_x_3569_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3610_ = v_x_3569_;
v_isShared_3611_ = v_isSharedCheck_3622_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_vs_3608_);
lean_dec(v_x_3569_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3622_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; uint8_t v___x_3615_; 
v___x_3612_ = lean_usize_to_nat(v_x_3570_);
v___x_3613_ = lean_array_get_size(v_vs_3608_);
v___x_3614_ = lean_box(0);
v___x_3615_ = lean_nat_dec_lt(v___x_3612_, v___x_3613_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3617_; 
lean_dec(v___x_3612_);
lean_dec_ref(v_vs_3608_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set_tag(v___x_3610_, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3614_);
v___x_3617_ = v___x_3610_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3614_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
else
{
size_t v___x_3619_; size_t v___x_3620_; lean_object* v___x_3621_; 
lean_del_object(v___x_3610_);
v___x_3619_ = lean_usize_of_nat(v___x_3612_);
lean_dec(v___x_3612_);
v___x_3620_ = lean_usize_of_nat(v___x_3613_);
v___x_3621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(v_vs_3608_, v___x_3619_, v___x_3620_, v___x_3614_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec_ref(v_vs_3608_);
return v___x_3621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3623_, lean_object* v_x_3624_, lean_object* v_x_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
size_t v_x_8219__boxed_3634_; size_t v_x_8220__boxed_3635_; lean_object* v_res_3636_; 
v_x_8219__boxed_3634_ = lean_unbox_usize(v_x_3624_);
lean_dec(v_x_3624_);
v_x_8220__boxed_3635_ = lean_unbox_usize(v_x_3625_);
lean_dec(v_x_3625_);
v_res_3636_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1(v_x_3623_, v_x_8219__boxed_3634_, v_x_8220__boxed_3635_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0(lean_object* v_t_3637_, lean_object* v_start_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3647_ = lean_unsigned_to_nat(0u);
v___x_3648_ = lean_nat_dec_eq(v_start_3638_, v___x_3647_);
if (v___x_3648_ == 0)
{
lean_object* v_root_3649_; lean_object* v_tail_3650_; size_t v_shift_3651_; lean_object* v_tailOff_3652_; uint8_t v___x_3653_; 
v_root_3649_ = lean_ctor_get(v_t_3637_, 0);
lean_inc_ref(v_root_3649_);
v_tail_3650_ = lean_ctor_get(v_t_3637_, 1);
lean_inc_ref(v_tail_3650_);
v_shift_3651_ = lean_ctor_get_usize(v_t_3637_, 4);
v_tailOff_3652_ = lean_ctor_get(v_t_3637_, 3);
lean_inc(v_tailOff_3652_);
lean_dec_ref(v_t_3637_);
v___x_3653_ = lean_nat_dec_le(v_tailOff_3652_, v_start_3638_);
if (v___x_3653_ == 0)
{
size_t v___x_3654_; lean_object* v___x_3655_; 
lean_dec(v_tailOff_3652_);
v___x_3654_ = lean_usize_of_nat(v_start_3638_);
v___x_3655_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1(v_root_3649_, v___x_3654_, v_shift_3651_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3668_; 
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; 
v_unused_3669_ = lean_ctor_get(v___x_3655_, 0);
lean_dec(v_unused_3669_);
v___x_3657_ = v___x_3655_;
v_isShared_3658_ = v_isSharedCheck_3668_;
goto v_resetjp_3656_;
}
else
{
lean_dec(v___x_3655_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3668_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v___x_3659_ = lean_array_get_size(v_tail_3650_);
v___x_3660_ = lean_box(0);
v___x_3661_ = lean_nat_dec_lt(v___x_3647_, v___x_3659_);
if (v___x_3661_ == 0)
{
lean_object* v___x_3663_; 
lean_dec_ref(v_tail_3650_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v___x_3660_);
v___x_3663_ = v___x_3657_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3660_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
else
{
size_t v___x_3665_; size_t v___x_3666_; lean_object* v___x_3667_; 
lean_del_object(v___x_3657_);
v___x_3665_ = ((size_t)0ULL);
v___x_3666_ = lean_usize_of_nat(v___x_3659_);
v___x_3667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(v_tail_3650_, v___x_3665_, v___x_3666_, v___x_3660_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
lean_dec_ref(v_tail_3650_);
return v___x_3667_;
}
}
}
else
{
lean_dec_ref(v_tail_3650_);
return v___x_3655_;
}
}
else
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
lean_dec_ref(v_root_3649_);
v___x_3670_ = lean_nat_sub(v_start_3638_, v_tailOff_3652_);
lean_dec(v_tailOff_3652_);
v___x_3671_ = lean_array_get_size(v_tail_3650_);
v___x_3672_ = lean_box(0);
v___x_3673_ = lean_nat_dec_lt(v___x_3670_, v___x_3671_);
if (v___x_3673_ == 0)
{
lean_object* v___x_3674_; 
lean_dec(v___x_3670_);
lean_dec_ref(v_tail_3650_);
v___x_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3672_);
return v___x_3674_;
}
else
{
size_t v___x_3675_; size_t v___x_3676_; lean_object* v___x_3677_; 
v___x_3675_ = lean_usize_of_nat(v___x_3670_);
lean_dec(v___x_3670_);
v___x_3676_ = lean_usize_of_nat(v___x_3671_);
v___x_3677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(v_tail_3650_, v___x_3675_, v___x_3676_, v___x_3672_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
lean_dec_ref(v_tail_3650_);
return v___x_3677_;
}
}
}
else
{
lean_object* v___x_3678_; 
v___x_3678_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__3(v_t_3637_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
return v___x_3678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0___boxed(lean_object* v_t_3679_, lean_object* v_start_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0(v_t_3679_, v_start_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec(v_start_3680_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0(lean_object* v_lctx_3690_, lean_object* v_start_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v_decls_3700_; lean_object* v___x_3701_; 
v_decls_3700_ = lean_ctor_get(v_lctx_3690_, 1);
lean_inc_ref(v_decls_3700_);
lean_dec_ref(v_lctx_3690_);
v___x_3701_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0(v_decls_3700_, v_start_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0___boxed(lean_object* v_lctx_3702_, lean_object* v_start_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0(v_lctx_3702_, v_start_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec(v_start_3703_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__1(lean_object* v_as_3713_, size_t v_i_3714_, size_t v_stop_3715_, lean_object* v_b_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
uint8_t v___x_3725_; 
v___x_3725_ = lean_usize_dec_eq(v_i_3714_, v_stop_3715_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = lean_array_uget_borrowed(v_as_3713_, v_i_3714_);
lean_inc(v___x_3726_);
v___x_3727_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processHyp(v___x_3726_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; size_t v___x_3729_; size_t v___x_3730_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3727_, 1);
v___x_3729_ = ((size_t)1ULL);
v___x_3730_ = lean_usize_add(v_i_3714_, v___x_3729_);
v_i_3714_ = v___x_3730_;
v_b_3716_ = v_a_3728_;
goto _start;
}
else
{
return v___x_3727_;
}
}
else
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v_b_3716_);
return v___x_3732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__1___boxed(lean_object* v_as_3733_, lean_object* v_i_3734_, lean_object* v_stop_3735_, lean_object* v_b_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
size_t v_i_boxed_3745_; size_t v_stop_boxed_3746_; lean_object* v_res_3747_; 
v_i_boxed_3745_ = lean_unbox_usize(v_i_3734_);
lean_dec(v_i_3734_);
v_stop_boxed_3746_ = lean_unbox_usize(v_stop_3735_);
lean_dec(v_stop_3735_);
v_res_3747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__1(v_as_3733_, v_i_boxed_3745_, v_stop_boxed_3746_, v_b_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v_as_3733_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem(lean_object* v_hyps_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___y_3760_; lean_object* v_lctx_3770_; lean_object* v___x_3771_; 
v___x_3756_ = lean_unsigned_to_nat(0u);
v___x_3757_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3);
v___x_3758_ = lean_st_mk_ref(v___x_3757_);
v_lctx_3770_ = lean_ctor_get(v_a_3751_, 2);
lean_inc_ref(v_lctx_3770_);
v___x_3771_ = l_Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0(v_lctx_3770_, v___x_3756_, v___x_3758_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v___x_3772_; 
lean_dec_ref_known(v___x_3771_, 1);
v___x_3772_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement(v___x_3758_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v___x_3773_; uint8_t v___x_3774_; 
lean_dec_ref_known(v___x_3772_, 1);
v___x_3773_ = lean_array_get_size(v_hyps_3748_);
v___x_3774_ = lean_nat_dec_lt(v___x_3756_, v___x_3773_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3775_; 
v___x_3775_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble(v___x_3758_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
v___y_3760_ = v___x_3775_;
goto v___jp_3759_;
}
else
{
lean_object* v___x_3776_; size_t v___x_3777_; size_t v___x_3778_; lean_object* v___x_3779_; 
v___x_3776_ = lean_box(0);
v___x_3777_ = ((size_t)0ULL);
v___x_3778_ = lean_usize_of_nat(v___x_3773_);
v___x_3779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__1(v_hyps_3748_, v___x_3777_, v___x_3778_, v___x_3776_, v___x_3758_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v___x_3780_; 
lean_dec_ref_known(v___x_3779_, 1);
v___x_3780_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble(v___x_3758_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
v___y_3760_ = v___x_3780_;
goto v___jp_3759_;
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec(v___x_3758_);
v_a_3781_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3779_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3779_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_dec(v___x_3758_);
v_a_3789_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3772_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3772_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec(v___x_3758_);
v_a_3797_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3771_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3771_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
v___jp_3759_:
{
if (lean_obj_tag(v___y_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3769_; 
v_a_3761_ = lean_ctor_get(v___y_3760_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___y_3760_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3763_ = v___y_3760_;
v_isShared_3764_ = v_isSharedCheck_3769_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___y_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3769_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3765_; lean_object* v___x_3767_; 
v___x_3765_ = lean_st_ref_get(v___x_3758_);
lean_dec(v___x_3758_);
lean_dec(v___x_3765_);
if (v_isShared_3764_ == 0)
{
v___x_3767_ = v___x_3763_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3761_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
else
{
lean_dec(v___x_3758_);
return v___y_3760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem___boxed(lean_object* v_hyps_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_){
_start:
{
lean_object* v_res_3813_; 
v_res_3813_ = l_Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem(v_hyps_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
lean_dec(v_a_3807_);
lean_dec_ref(v_a_3806_);
lean_dec_ref(v_hyps_3805_);
return v_res_3813_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3814_ = lean_unsigned_to_nat(32u);
v___x_3815_ = lean_mk_empty_array_with_capacity(v___x_3814_);
v___x_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
return v___x_3816_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__1(void){
_start:
{
size_t v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3817_ = ((size_t)5ULL);
v___x_3818_ = lean_unsigned_to_nat(0u);
v___x_3819_ = lean_unsigned_to_nat(32u);
v___x_3820_ = lean_mk_empty_array_with_capacity(v___x_3819_);
v___x_3821_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__0);
v___x_3822_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
lean_ctor_set(v___x_3822_, 1, v___x_3820_);
lean_ctor_set(v___x_3822_, 2, v___x_3818_);
lean_ctor_set(v___x_3822_, 3, v___x_3818_);
lean_ctor_set_usize(v___x_3822_, 4, v___x_3817_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg(lean_object* v___y_3823_){
_start:
{
lean_object* v___x_3825_; lean_object* v_traceState_3826_; lean_object* v_traces_3827_; lean_object* v___x_3828_; lean_object* v_traceState_3829_; lean_object* v_env_3830_; lean_object* v_nextMacroScope_3831_; lean_object* v_ngen_3832_; lean_object* v_auxDeclNGen_3833_; lean_object* v_cache_3834_; lean_object* v_recordedDeps_3835_; lean_object* v_messages_3836_; lean_object* v_infoState_3837_; lean_object* v_snapshotTasks_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3857_; 
v___x_3825_ = lean_st_ref_get(v___y_3823_);
v_traceState_3826_ = lean_ctor_get(v___x_3825_, 4);
lean_inc_ref(v_traceState_3826_);
lean_dec(v___x_3825_);
v_traces_3827_ = lean_ctor_get(v_traceState_3826_, 0);
lean_inc_ref(v_traces_3827_);
lean_dec_ref(v_traceState_3826_);
v___x_3828_ = lean_st_ref_take(v___y_3823_);
v_traceState_3829_ = lean_ctor_get(v___x_3828_, 4);
v_env_3830_ = lean_ctor_get(v___x_3828_, 0);
v_nextMacroScope_3831_ = lean_ctor_get(v___x_3828_, 1);
v_ngen_3832_ = lean_ctor_get(v___x_3828_, 2);
v_auxDeclNGen_3833_ = lean_ctor_get(v___x_3828_, 3);
v_cache_3834_ = lean_ctor_get(v___x_3828_, 5);
v_recordedDeps_3835_ = lean_ctor_get(v___x_3828_, 6);
v_messages_3836_ = lean_ctor_get(v___x_3828_, 7);
v_infoState_3837_ = lean_ctor_get(v___x_3828_, 8);
v_snapshotTasks_3838_ = lean_ctor_get(v___x_3828_, 9);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3840_ = v___x_3828_;
v_isShared_3841_ = v_isSharedCheck_3857_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_snapshotTasks_3838_);
lean_inc(v_infoState_3837_);
lean_inc(v_messages_3836_);
lean_inc(v_recordedDeps_3835_);
lean_inc(v_cache_3834_);
lean_inc(v_traceState_3829_);
lean_inc(v_auxDeclNGen_3833_);
lean_inc(v_ngen_3832_);
lean_inc(v_nextMacroScope_3831_);
lean_inc(v_env_3830_);
lean_dec(v___x_3828_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3857_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
uint64_t v_tid_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3855_; 
v_tid_3842_ = lean_ctor_get_uint64(v_traceState_3829_, sizeof(void*)*1);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_traceState_3829_);
if (v_isSharedCheck_3855_ == 0)
{
lean_object* v_unused_3856_; 
v_unused_3856_ = lean_ctor_get(v_traceState_3829_, 0);
lean_dec(v_unused_3856_);
v___x_3844_ = v_traceState_3829_;
v_isShared_3845_ = v_isSharedCheck_3855_;
goto v_resetjp_3843_;
}
else
{
lean_dec(v_traceState_3829_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3855_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3846_; lean_object* v___x_3848_; 
v___x_3846_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__1);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 0, v___x_3846_);
v___x_3848_ = v___x_3844_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3846_);
lean_ctor_set_uint64(v_reuseFailAlloc_3854_, sizeof(void*)*1, v_tid_3842_);
v___x_3848_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
lean_object* v___x_3850_; 
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 4, v___x_3848_);
v___x_3850_ = v___x_3840_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_env_3830_);
lean_ctor_set(v_reuseFailAlloc_3853_, 1, v_nextMacroScope_3831_);
lean_ctor_set(v_reuseFailAlloc_3853_, 2, v_ngen_3832_);
lean_ctor_set(v_reuseFailAlloc_3853_, 3, v_auxDeclNGen_3833_);
lean_ctor_set(v_reuseFailAlloc_3853_, 4, v___x_3848_);
lean_ctor_set(v_reuseFailAlloc_3853_, 5, v_cache_3834_);
lean_ctor_set(v_reuseFailAlloc_3853_, 6, v_recordedDeps_3835_);
lean_ctor_set(v_reuseFailAlloc_3853_, 7, v_messages_3836_);
lean_ctor_set(v_reuseFailAlloc_3853_, 8, v_infoState_3837_);
lean_ctor_set(v_reuseFailAlloc_3853_, 9, v_snapshotTasks_3838_);
v___x_3850_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = lean_st_ref_put(v___y_3823_, v___x_3850_);
v___x_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3852_, 0, v_traces_3827_);
return v___x_3852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___boxed(lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg(v___y_3858_);
lean_dec(v___y_3858_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14(lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg(v___y_3864_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___boxed(lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14(v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
return v_res_3872_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15(lean_object* v_opts_3873_, lean_object* v_opt_3874_){
_start:
{
lean_object* v_name_3875_; lean_object* v_defValue_3876_; lean_object* v_map_3877_; lean_object* v___x_3878_; 
v_name_3875_ = lean_ctor_get(v_opt_3874_, 0);
v_defValue_3876_ = lean_ctor_get(v_opt_3874_, 1);
v_map_3877_ = lean_ctor_get(v_opts_3873_, 0);
v___x_3878_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3877_, v_name_3875_);
if (lean_obj_tag(v___x_3878_) == 0)
{
uint8_t v___x_3879_; 
v___x_3879_ = lean_unbox(v_defValue_3876_);
return v___x_3879_;
}
else
{
lean_object* v_val_3880_; 
v_val_3880_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_val_3880_);
lean_dec_ref_known(v___x_3878_, 1);
if (lean_obj_tag(v_val_3880_) == 1)
{
uint8_t v_v_3881_; 
v_v_3881_ = lean_ctor_get_uint8(v_val_3880_, 0);
lean_dec_ref_known(v_val_3880_, 0);
return v_v_3881_;
}
else
{
uint8_t v___x_3882_; 
lean_dec(v_val_3880_);
v___x_3882_ = lean_unbox(v_defValue_3876_);
return v___x_3882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15___boxed(lean_object* v_opts_3883_, lean_object* v_opt_3884_){
_start:
{
uint8_t v_res_3885_; lean_object* v_r_3886_; 
v_res_3885_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15(v_opts_3883_, v_opt_3884_);
lean_dec_ref(v_opt_3884_);
lean_dec_ref(v_opts_3883_);
v_r_3886_ = lean_box(v_res_3885_);
return v_r_3886_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__0));
v___x_3889_ = l_Lean_stringToMessageData(v___x_3888_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0(lean_object* v_x_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__1);
v___x_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___boxed(lean_object* v_x_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0(v_x_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec_ref(v_x_3898_);
return v_res_3904_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3908_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__1));
v___x_3909_ = l_Lean_MessageData_ofFormat(v___x_3908_);
return v___x_3909_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3910_ = lean_box(1);
v___x_3911_ = l_Lean_MessageData_ofFormat(v___x_3910_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2(lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
if (lean_obj_tag(v_a_3912_) == 0)
{
lean_object* v___x_3914_; 
v___x_3914_ = l_List_reverse___redArg(v_a_3913_);
return v___x_3914_;
}
else
{
lean_object* v_head_3915_; lean_object* v_tail_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3942_; 
v_head_3915_ = lean_ctor_get(v_a_3912_, 0);
v_tail_3916_ = lean_ctor_get(v_a_3912_, 1);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_a_3912_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3918_ = v_a_3912_;
v_isShared_3919_ = v_isSharedCheck_3942_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_tail_3916_);
lean_inc(v_head_3915_);
lean_dec(v_a_3912_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3942_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v_fst_3920_; lean_object* v_snd_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3941_; 
v_fst_3920_ = lean_ctor_get(v_head_3915_, 0);
v_snd_3921_ = lean_ctor_get(v_head_3915_, 1);
v_isSharedCheck_3941_ = !lean_is_exclusive(v_head_3915_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3923_ = v_head_3915_;
v_isShared_3924_ = v_isSharedCheck_3941_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_snd_3921_);
lean_inc(v_fst_3920_);
lean_dec(v_head_3915_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3941_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3930_; 
v___x_3925_ = l_Nat_reprFast(v_fst_3920_);
v___x_3926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
v___x_3927_ = l_Lean_MessageData_ofFormat(v___x_3926_);
v___x_3928_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__2);
if (v_isShared_3924_ == 0)
{
lean_ctor_set_tag(v___x_3923_, 7);
lean_ctor_set(v___x_3923_, 1, v___x_3928_);
lean_ctor_set(v___x_3923_, 0, v___x_3927_);
v___x_3930_ = v___x_3923_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v___x_3928_);
v___x_3930_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3931_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__3);
v___x_3932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3930_);
lean_ctor_set(v___x_3932_, 1, v___x_3931_);
v___x_3933_ = l_Lean_MessageData_ofExpr(v_snd_3921_);
v___x_3934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3932_);
lean_ctor_set(v___x_3934_, 1, v___x_3933_);
v___x_3935_ = l_Lean_MessageData_paren(v___x_3934_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 1, v_a_3913_);
lean_ctor_set(v___x_3918_, 0, v___x_3935_);
v___x_3937_ = v___x_3918_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3935_);
lean_ctor_set(v_reuseFailAlloc_3939_, 1, v_a_3913_);
v___x_3937_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
v_a_3912_ = v_tail_3916_;
v_a_3913_ = v___x_3937_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3(lean_object* v_cls_3943_, lean_object* v_msg_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_ref_3950_; lean_object* v___x_3951_; lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3997_; 
v_ref_3950_ = lean_ctor_get(v___y_3947_, 2);
v___x_3951_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2_spec__3(v_msg_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3954_ = v___x_3951_;
v_isShared_3955_ = v_isSharedCheck_3997_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v___x_3951_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3997_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v_traceState_3957_; lean_object* v_env_3958_; lean_object* v_nextMacroScope_3959_; lean_object* v_ngen_3960_; lean_object* v_auxDeclNGen_3961_; lean_object* v_cache_3962_; lean_object* v_recordedDeps_3963_; lean_object* v_messages_3964_; lean_object* v_infoState_3965_; lean_object* v_snapshotTasks_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3996_; 
v___x_3956_ = lean_st_ref_take(v___y_3948_);
v_traceState_3957_ = lean_ctor_get(v___x_3956_, 4);
v_env_3958_ = lean_ctor_get(v___x_3956_, 0);
v_nextMacroScope_3959_ = lean_ctor_get(v___x_3956_, 1);
v_ngen_3960_ = lean_ctor_get(v___x_3956_, 2);
v_auxDeclNGen_3961_ = lean_ctor_get(v___x_3956_, 3);
v_cache_3962_ = lean_ctor_get(v___x_3956_, 5);
v_recordedDeps_3963_ = lean_ctor_get(v___x_3956_, 6);
v_messages_3964_ = lean_ctor_get(v___x_3956_, 7);
v_infoState_3965_ = lean_ctor_get(v___x_3956_, 8);
v_snapshotTasks_3966_ = lean_ctor_get(v___x_3956_, 9);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3968_ = v___x_3956_;
v_isShared_3969_ = v_isSharedCheck_3996_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_snapshotTasks_3966_);
lean_inc(v_infoState_3965_);
lean_inc(v_messages_3964_);
lean_inc(v_recordedDeps_3963_);
lean_inc(v_cache_3962_);
lean_inc(v_traceState_3957_);
lean_inc(v_auxDeclNGen_3961_);
lean_inc(v_ngen_3960_);
lean_inc(v_nextMacroScope_3959_);
lean_inc(v_env_3958_);
lean_dec(v___x_3956_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3996_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
uint64_t v_tid_3970_; lean_object* v_traces_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3995_; 
v_tid_3970_ = lean_ctor_get_uint64(v_traceState_3957_, sizeof(void*)*1);
v_traces_3971_ = lean_ctor_get(v_traceState_3957_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_traceState_3957_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3973_ = v_traceState_3957_;
v_isShared_3974_ = v_isSharedCheck_3995_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_traces_3971_);
lean_dec(v_traceState_3957_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3995_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; double v___x_3977_; uint8_t v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3986_; 
v___x_3975_ = lean_box(0);
v___x_3976_ = lean_box(0);
v___x_3977_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0);
v___x_3978_ = 0;
v___x_3979_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__1));
v___x_3980_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3980_, 0, v_cls_3943_);
lean_ctor_set(v___x_3980_, 1, v___x_3976_);
lean_ctor_set(v___x_3980_, 2, v___x_3979_);
lean_ctor_set_float(v___x_3980_, sizeof(void*)*3, v___x_3977_);
lean_ctor_set_float(v___x_3980_, sizeof(void*)*3 + 8, v___x_3977_);
lean_ctor_set_uint8(v___x_3980_, sizeof(void*)*3 + 16, v___x_3978_);
v___x_3981_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__2));
v___x_3982_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3980_);
lean_ctor_set(v___x_3982_, 1, v_a_3952_);
lean_ctor_set(v___x_3982_, 2, v___x_3981_);
lean_inc(v_ref_3950_);
v___x_3983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3983_, 0, v_ref_3950_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
v___x_3984_ = l_Lean_PersistentArray_push___redArg(v_traces_3971_, v___x_3983_);
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 0, v___x_3984_);
v___x_3986_ = v___x_3973_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3984_);
lean_ctor_set_uint64(v_reuseFailAlloc_3994_, sizeof(void*)*1, v_tid_3970_);
v___x_3986_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
lean_object* v___x_3988_; 
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 4, v___x_3986_);
v___x_3988_ = v___x_3968_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_env_3958_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_nextMacroScope_3959_);
lean_ctor_set(v_reuseFailAlloc_3993_, 2, v_ngen_3960_);
lean_ctor_set(v_reuseFailAlloc_3993_, 3, v_auxDeclNGen_3961_);
lean_ctor_set(v_reuseFailAlloc_3993_, 4, v___x_3986_);
lean_ctor_set(v_reuseFailAlloc_3993_, 5, v_cache_3962_);
lean_ctor_set(v_reuseFailAlloc_3993_, 6, v_recordedDeps_3963_);
lean_ctor_set(v_reuseFailAlloc_3993_, 7, v_messages_3964_);
lean_ctor_set(v_reuseFailAlloc_3993_, 8, v_infoState_3965_);
lean_ctor_set(v_reuseFailAlloc_3993_, 9, v_snapshotTasks_3966_);
v___x_3988_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
lean_object* v___x_3989_; lean_object* v___x_3991_; 
v___x_3989_ = lean_st_ref_put(v___y_3948_, v___x_3988_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 0, v___x_3975_);
v___x_3991_ = v___x_3954_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3975_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3___boxed(lean_object* v_cls_3998_, lean_object* v_msg_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3(v_cls_3998_, v_msg_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0_spec__3(lean_object* v_msg_4006_){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default;
v___x_4008_ = lean_panic_fn_borrowed(v___x_4007_, v_msg_4006_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0(lean_object* v_a_4009_, lean_object* v_x_4010_){
_start:
{
if (lean_obj_tag(v_x_4010_) == 0)
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4011_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0_spec__0___closed__3);
v___x_4012_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0_spec__3(v___x_4011_);
return v___x_4012_;
}
else
{
lean_object* v_key_4013_; lean_object* v_value_4014_; lean_object* v_tail_4015_; uint8_t v___x_4016_; 
v_key_4013_ = lean_ctor_get(v_x_4010_, 0);
v_value_4014_ = lean_ctor_get(v_x_4010_, 1);
v_tail_4015_ = lean_ctor_get(v_x_4010_, 2);
v___x_4016_ = lean_nat_dec_eq(v_key_4013_, v_a_4009_);
if (v___x_4016_ == 0)
{
v_x_4010_ = v_tail_4015_;
goto _start;
}
else
{
lean_inc(v_value_4014_);
return v_value_4014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0___boxed(lean_object* v_a_4018_, lean_object* v_x_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0(v_a_4018_, v_x_4019_);
lean_dec(v_x_4019_);
lean_dec(v_a_4018_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0(lean_object* v_m_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v_buckets_4023_; lean_object* v___x_4024_; uint64_t v___x_4025_; uint64_t v___x_4026_; uint64_t v___x_4027_; uint64_t v_fold_4028_; uint64_t v___x_4029_; uint64_t v___x_4030_; uint64_t v___x_4031_; size_t v___x_4032_; size_t v___x_4033_; size_t v___x_4034_; size_t v___x_4035_; size_t v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v_buckets_4023_ = lean_ctor_get(v_m_4021_, 1);
v___x_4024_ = lean_array_get_size(v_buckets_4023_);
v___x_4025_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_a_4022_);
v___x_4026_ = 32ULL;
v___x_4027_ = lean_uint64_shift_right(v___x_4025_, v___x_4026_);
v_fold_4028_ = lean_uint64_xor(v___x_4025_, v___x_4027_);
v___x_4029_ = 16ULL;
v___x_4030_ = lean_uint64_shift_right(v_fold_4028_, v___x_4029_);
v___x_4031_ = lean_uint64_xor(v_fold_4028_, v___x_4030_);
v___x_4032_ = lean_uint64_to_usize(v___x_4031_);
v___x_4033_ = lean_usize_of_nat(v___x_4024_);
v___x_4034_ = ((size_t)1ULL);
v___x_4035_ = lean_usize_sub(v___x_4033_, v___x_4034_);
v___x_4036_ = lean_usize_land(v___x_4032_, v___x_4035_);
v___x_4037_ = lean_array_uget_borrowed(v_buckets_4023_, v___x_4036_);
v___x_4038_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0(v_a_4022_, v___x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0___boxed(lean_object* v_m_4039_, lean_object* v_a_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0(v_m_4039_, v_a_4040_);
lean_dec(v_a_4040_);
lean_dec_ref(v_m_4039_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__1(lean_object* v___x_4042_, size_t v_sz_4043_, size_t v_i_4044_, lean_object* v_bs_4045_){
_start:
{
uint8_t v___x_4046_; 
v___x_4046_ = lean_usize_dec_lt(v_i_4044_, v_sz_4043_);
if (v___x_4046_ == 0)
{
return v_bs_4045_;
}
else
{
lean_object* v_v_4047_; lean_object* v___x_4048_; lean_object* v_type_4049_; lean_object* v___x_4050_; lean_object* v_bs_x27_4051_; lean_object* v___x_4052_; size_t v___x_4053_; size_t v___x_4054_; lean_object* v___x_4055_; 
v_v_4047_ = lean_array_uget(v_bs_4045_, v_i_4044_);
v___x_4048_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0(v___x_4042_, v_v_4047_);
v_type_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc_ref(v_type_4049_);
lean_dec_ref(v___x_4048_);
v___x_4050_ = lean_unsigned_to_nat(0u);
v_bs_x27_4051_ = lean_array_uset(v_bs_4045_, v_i_4044_, v___x_4050_);
v___x_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4052_, 0, v_v_4047_);
lean_ctor_set(v___x_4052_, 1, v_type_4049_);
v___x_4053_ = ((size_t)1ULL);
v___x_4054_ = lean_usize_add(v_i_4044_, v___x_4053_);
v___x_4055_ = lean_array_uset(v_bs_x27_4051_, v_i_4044_, v___x_4052_);
v_i_4044_ = v___x_4054_;
v_bs_4045_ = v___x_4055_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__1___boxed(lean_object* v___x_4057_, lean_object* v_sz_4058_, lean_object* v_i_4059_, lean_object* v_bs_4060_){
_start:
{
size_t v_sz_boxed_4061_; size_t v_i_boxed_4062_; lean_object* v_res_4063_; 
v_sz_boxed_4061_ = lean_unbox_usize(v_sz_4058_);
lean_dec(v_sz_4058_);
v_i_boxed_4062_ = lean_unbox_usize(v_i_4059_);
lean_dec(v_i_4059_);
v_res_4063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__1(v___x_4057_, v_sz_boxed_4061_, v_i_boxed_4062_, v_bs_4060_);
lean_dec_ref(v___x_4057_);
return v_res_4063_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__1(void){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__0));
v___x_4066_ = l_Lean_stringToMessageData(v___x_4065_);
return v___x_4066_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__3(void){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__2));
v___x_4069_ = l_Lean_stringToMessageData(v___x_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8(lean_object* v___x_4070_, lean_object* v_as_4071_, size_t v_sz_4072_, size_t v_i_4073_, lean_object* v_b_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v_a_4081_; uint8_t v___x_4085_; 
v___x_4085_ = lean_usize_dec_lt(v_i_4073_, v_sz_4072_);
if (v___x_4085_ == 0)
{
lean_object* v___x_4086_; 
v___x_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4086_, 0, v_b_4074_);
return v___x_4086_;
}
else
{
lean_object* v_a_4087_; lean_object* v_snd_4088_; lean_object* v_toCold_4089_; lean_object* v_options_4090_; lean_object* v_fst_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4118_; 
v_a_4087_ = lean_array_uget(v_as_4071_, v_i_4073_);
v_snd_4088_ = lean_ctor_get(v_a_4087_, 1);
lean_inc(v_snd_4088_);
v_toCold_4089_ = lean_ctor_get(v___y_4077_, 0);
v_options_4090_ = lean_ctor_get(v_toCold_4089_, 2);
v_fst_4091_ = lean_ctor_get(v_a_4087_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v_a_4087_);
if (v_isSharedCheck_4118_ == 0)
{
lean_object* v_unused_4119_; 
v_unused_4119_ = lean_ctor_get(v_a_4087_, 1);
lean_dec(v_unused_4119_);
v___x_4093_ = v_a_4087_;
v_isShared_4094_ = v_isSharedCheck_4118_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_fst_4091_);
lean_dec(v_a_4087_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4118_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v_argumentSorts_4095_; lean_object* v_inheritedTraceOptions_4096_; uint8_t v_hasTrace_4097_; lean_object* v___x_4098_; 
v_argumentSorts_4095_ = lean_ctor_get(v_snd_4088_, 0);
lean_inc_ref(v_argumentSorts_4095_);
lean_dec(v_snd_4088_);
v_inheritedTraceOptions_4096_ = lean_ctor_get(v_toCold_4089_, 11);
v_hasTrace_4097_ = lean_ctor_get_uint8(v_options_4090_, sizeof(void*)*1);
v___x_4098_ = lean_box(0);
if (v_hasTrace_4097_ == 0)
{
lean_dec_ref(v_argumentSorts_4095_);
lean_del_object(v___x_4093_);
lean_dec(v_fst_4091_);
v_a_4081_ = v___x_4098_;
goto v___jp_4080_;
}
else
{
lean_object* v_cls_4099_; lean_object* v___x_4100_; uint8_t v___x_4101_; 
v_cls_4099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_4100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9);
v___x_4101_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4096_, v_options_4090_, v___x_4100_);
if (v___x_4101_ == 0)
{
lean_dec_ref(v_argumentSorts_4095_);
lean_del_object(v___x_4093_);
lean_dec(v_fst_4091_);
v_a_4081_ = v___x_4098_;
goto v___jp_4080_;
}
else
{
size_t v_sz_4102_; size_t v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4108_; 
v_sz_4102_ = lean_array_size(v_argumentSorts_4095_);
v___x_4103_ = ((size_t)0ULL);
v___x_4104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__1(v___x_4070_, v_sz_4102_, v___x_4103_, v_argumentSorts_4095_);
v___x_4105_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__1);
v___x_4106_ = l_Lean_MessageData_ofExpr(v_fst_4091_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set_tag(v___x_4093_, 7);
lean_ctor_set(v___x_4093_, 1, v___x_4106_);
lean_ctor_set(v___x_4093_, 0, v___x_4105_);
v___x_4108_ = v___x_4093_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v___x_4105_);
lean_ctor_set(v_reuseFailAlloc_4117_, 1, v___x_4106_);
v___x_4108_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__3);
v___x_4110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4108_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = lean_array_to_list(v___x_4104_);
v___x_4112_ = lean_box(0);
v___x_4113_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2(v___x_4111_, v___x_4112_);
v___x_4114_ = l_Lean_MessageData_ofList(v___x_4113_);
v___x_4115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4110_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
v___x_4116_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3(v_cls_4099_, v___x_4115_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_dec_ref_known(v___x_4116_, 1);
v_a_4081_ = v___x_4098_;
goto v___jp_4080_;
}
else
{
return v___x_4116_;
}
}
}
}
}
}
v___jp_4080_:
{
size_t v___x_4082_; size_t v___x_4083_; 
v___x_4082_ = ((size_t)1ULL);
v___x_4083_ = lean_usize_add(v_i_4073_, v___x_4082_);
v_i_4073_ = v___x_4083_;
v_b_4074_ = v_a_4081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___boxed(lean_object* v___x_4120_, lean_object* v_as_4121_, lean_object* v_sz_4122_, lean_object* v_i_4123_, lean_object* v_b_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
size_t v_sz_boxed_4130_; size_t v_i_boxed_4131_; lean_object* v_res_4132_; 
v_sz_boxed_4130_ = lean_unbox_usize(v_sz_4122_);
lean_dec(v_sz_4122_);
v_i_boxed_4131_ = lean_unbox_usize(v_i_4123_);
lean_dec(v_i_4123_);
v_res_4132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8(v___x_4120_, v_as_4121_, v_sz_boxed_4130_, v_i_boxed_4131_, v_b_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec_ref(v_as_4121_);
lean_dec_ref(v___x_4120_);
return v_res_4132_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__0));
v___x_4135_ = l_Lean_stringToMessageData(v___x_4134_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9(lean_object* v_as_4136_, size_t v_sz_4137_, size_t v_i_4138_, lean_object* v_b_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v_a_4146_; uint8_t v___x_4150_; 
v___x_4150_ = lean_usize_dec_lt(v_i_4138_, v_sz_4137_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4151_; 
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v_b_4139_);
return v___x_4151_;
}
else
{
lean_object* v_toCold_4152_; lean_object* v_options_4153_; lean_object* v_inheritedTraceOptions_4154_; uint8_t v_hasTrace_4155_; lean_object* v___x_4156_; 
v_toCold_4152_ = lean_ctor_get(v___y_4142_, 0);
v_options_4153_ = lean_ctor_get(v_toCold_4152_, 2);
v_inheritedTraceOptions_4154_ = lean_ctor_get(v_toCold_4152_, 11);
v_hasTrace_4155_ = lean_ctor_get_uint8(v_options_4153_, sizeof(void*)*1);
v___x_4156_ = lean_box(0);
if (v_hasTrace_4155_ == 0)
{
v_a_4146_ = v___x_4156_;
goto v___jp_4145_;
}
else
{
lean_object* v_cls_4157_; lean_object* v___x_4158_; uint8_t v___x_4159_; 
v_cls_4157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_4158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9);
v___x_4159_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4154_, v_options_4153_, v___x_4158_);
if (v___x_4159_ == 0)
{
v_a_4146_ = v___x_4156_;
goto v___jp_4145_;
}
else
{
lean_object* v_a_4160_; lean_object* v_type_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_a_4160_ = lean_array_uget_borrowed(v_as_4136_, v_i_4138_);
v_type_4161_ = lean_ctor_get(v_a_4160_, 1);
v___x_4162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__1);
lean_inc_ref(v_type_4161_);
v___x_4163_ = l_Lean_MessageData_ofExpr(v_type_4161_);
v___x_4164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4162_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3(v_cls_4157_, v___x_4164_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_dec_ref_known(v___x_4165_, 1);
v_a_4146_ = v___x_4156_;
goto v___jp_4145_;
}
else
{
return v___x_4165_;
}
}
}
}
v___jp_4145_:
{
size_t v___x_4147_; size_t v___x_4148_; 
v___x_4147_ = ((size_t)1ULL);
v___x_4148_ = lean_usize_add(v_i_4138_, v___x_4147_);
v_i_4138_ = v___x_4148_;
v_b_4139_ = v_a_4146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___boxed(lean_object* v_as_4166_, lean_object* v_sz_4167_, lean_object* v_i_4168_, lean_object* v_b_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
size_t v_sz_boxed_4175_; size_t v_i_boxed_4176_; lean_object* v_res_4177_; 
v_sz_boxed_4175_ = lean_unbox_usize(v_sz_4167_);
lean_dec(v_sz_4167_);
v_i_boxed_4176_ = lean_unbox_usize(v_i_4168_);
lean_dec(v_i_4168_);
v_res_4177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9(v_as_4166_, v_sz_boxed_4175_, v_i_boxed_4176_, v_b_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec_ref(v_as_4166_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__12(lean_object* v_x_4178_, lean_object* v_x_4179_){
_start:
{
if (lean_obj_tag(v_x_4179_) == 0)
{
return v_x_4178_;
}
else
{
lean_object* v_key_4180_; lean_object* v_value_4181_; lean_object* v_tail_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v_key_4180_ = lean_ctor_get(v_x_4179_, 0);
v_value_4181_ = lean_ctor_get(v_x_4179_, 1);
v_tail_4182_ = lean_ctor_get(v_x_4179_, 2);
lean_inc(v_value_4181_);
lean_inc(v_key_4180_);
v___x_4183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4183_, 0, v_key_4180_);
lean_ctor_set(v___x_4183_, 1, v_value_4181_);
v___x_4184_ = lean_array_push(v_x_4178_, v___x_4183_);
v_x_4178_ = v___x_4184_;
v_x_4179_ = v_tail_4182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__12___boxed(lean_object* v_x_4186_, lean_object* v_x_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__12(v_x_4186_, v_x_4187_);
lean_dec(v_x_4187_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13(lean_object* v_as_4189_, size_t v_i_4190_, size_t v_stop_4191_, lean_object* v_b_4192_){
_start:
{
uint8_t v___x_4193_; 
v___x_4193_ = lean_usize_dec_eq(v_i_4190_, v_stop_4191_);
if (v___x_4193_ == 0)
{
lean_object* v___x_4194_; lean_object* v___x_4195_; size_t v___x_4196_; size_t v___x_4197_; 
v___x_4194_ = lean_array_uget_borrowed(v_as_4189_, v_i_4190_);
v___x_4195_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__12(v_b_4192_, v___x_4194_);
v___x_4196_ = ((size_t)1ULL);
v___x_4197_ = lean_usize_add(v_i_4190_, v___x_4196_);
v_i_4190_ = v___x_4197_;
v_b_4192_ = v___x_4195_;
goto _start;
}
else
{
return v_b_4192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13___boxed(lean_object* v_as_4199_, lean_object* v_i_4200_, lean_object* v_stop_4201_, lean_object* v_b_4202_){
_start:
{
size_t v_i_boxed_4203_; size_t v_stop_boxed_4204_; lean_object* v_res_4205_; 
v_i_boxed_4203_ = lean_unbox_usize(v_i_4200_);
lean_dec(v_i_4200_);
v_stop_boxed_4204_ = lean_unbox_usize(v_stop_4201_);
lean_dec(v_stop_4201_);
v_res_4205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13(v_as_4199_, v_i_boxed_4203_, v_stop_boxed_4204_, v_b_4202_);
lean_dec_ref(v_as_4199_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___redArg(lean_object* v_hi_4206_, lean_object* v_pivot_4207_, lean_object* v_as_4208_, lean_object* v_i_4209_, lean_object* v_k_4210_){
_start:
{
uint8_t v___x_4211_; 
v___x_4211_ = lean_nat_dec_lt(v_k_4210_, v_hi_4206_);
if (v___x_4211_ == 0)
{
lean_object* v___x_4212_; lean_object* v___x_4213_; 
lean_dec(v_k_4210_);
v___x_4212_ = lean_array_fswap(v_as_4208_, v_i_4209_, v_hi_4206_);
v___x_4213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4213_, 0, v_i_4209_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
return v___x_4213_;
}
else
{
lean_object* v___x_4214_; lean_object* v_fst_4215_; lean_object* v_fst_4216_; uint8_t v___x_4217_; 
v___x_4214_ = lean_array_fget_borrowed(v_as_4208_, v_k_4210_);
v_fst_4215_ = lean_ctor_get(v___x_4214_, 0);
v_fst_4216_ = lean_ctor_get(v_pivot_4207_, 0);
v___x_4217_ = lean_expr_lt(v_fst_4215_, v_fst_4216_);
if (v___x_4217_ == 0)
{
lean_object* v___x_4218_; lean_object* v___x_4219_; 
v___x_4218_ = lean_unsigned_to_nat(1u);
v___x_4219_ = lean_nat_add(v_k_4210_, v___x_4218_);
lean_dec(v_k_4210_);
v_k_4210_ = v___x_4219_;
goto _start;
}
else
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4221_ = lean_array_fswap(v_as_4208_, v_i_4209_, v_k_4210_);
v___x_4222_ = lean_unsigned_to_nat(1u);
v___x_4223_ = lean_nat_add(v_i_4209_, v___x_4222_);
lean_dec(v_i_4209_);
v___x_4224_ = lean_nat_add(v_k_4210_, v___x_4222_);
lean_dec(v_k_4210_);
v_as_4208_ = v___x_4221_;
v_i_4209_ = v___x_4223_;
v_k_4210_ = v___x_4224_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___redArg___boxed(lean_object* v_hi_4226_, lean_object* v_pivot_4227_, lean_object* v_as_4228_, lean_object* v_i_4229_, lean_object* v_k_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___redArg(v_hi_4226_, v_pivot_4227_, v_as_4228_, v_i_4229_, v_k_4230_);
lean_dec_ref(v_pivot_4227_);
lean_dec(v_hi_4226_);
return v_res_4231_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0(lean_object* v_x1_4232_, lean_object* v_x2_4233_){
_start:
{
lean_object* v_fst_4234_; lean_object* v_fst_4235_; uint8_t v___x_4236_; 
v_fst_4234_ = lean_ctor_get(v_x1_4232_, 0);
v_fst_4235_ = lean_ctor_get(v_x2_4233_, 0);
v___x_4236_ = lean_expr_lt(v_fst_4234_, v_fst_4235_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0___boxed(lean_object* v_x1_4237_, lean_object* v_x2_4238_){
_start:
{
uint8_t v_res_4239_; lean_object* v_r_4240_; 
v_res_4239_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0(v_x1_4237_, v_x2_4238_);
lean_dec_ref(v_x2_4238_);
lean_dec_ref(v_x1_4237_);
v_r_4240_ = lean_box(v_res_4239_);
return v_r_4240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(lean_object* v_n_4241_, lean_object* v_as_4242_, lean_object* v_lo_4243_, lean_object* v_hi_4244_){
_start:
{
lean_object* v___y_4246_; uint8_t v___x_4256_; 
v___x_4256_ = lean_nat_dec_lt(v_lo_4243_, v_hi_4244_);
if (v___x_4256_ == 0)
{
lean_dec(v_lo_4243_);
return v_as_4242_;
}
else
{
lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v_mid_4259_; lean_object* v___y_4261_; lean_object* v___y_4267_; lean_object* v___x_4272_; lean_object* v___x_4273_; uint8_t v___x_4274_; 
v___x_4257_ = lean_nat_add(v_lo_4243_, v_hi_4244_);
v___x_4258_ = lean_unsigned_to_nat(1u);
v_mid_4259_ = lean_nat_shiftr(v___x_4257_, v___x_4258_);
lean_dec(v___x_4257_);
v___x_4272_ = lean_array_fget_borrowed(v_as_4242_, v_mid_4259_);
v___x_4273_ = lean_array_fget_borrowed(v_as_4242_, v_lo_4243_);
v___x_4274_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0(v___x_4272_, v___x_4273_);
if (v___x_4274_ == 0)
{
v___y_4267_ = v_as_4242_;
goto v___jp_4266_;
}
else
{
lean_object* v___x_4275_; 
v___x_4275_ = lean_array_fswap(v_as_4242_, v_lo_4243_, v_mid_4259_);
v___y_4267_ = v___x_4275_;
goto v___jp_4266_;
}
v___jp_4260_:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; uint8_t v___x_4264_; 
v___x_4262_ = lean_array_fget_borrowed(v___y_4261_, v_mid_4259_);
v___x_4263_ = lean_array_fget_borrowed(v___y_4261_, v_hi_4244_);
v___x_4264_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0(v___x_4262_, v___x_4263_);
if (v___x_4264_ == 0)
{
lean_dec(v_mid_4259_);
v___y_4246_ = v___y_4261_;
goto v___jp_4245_;
}
else
{
lean_object* v___x_4265_; 
v___x_4265_ = lean_array_fswap(v___y_4261_, v_mid_4259_, v_hi_4244_);
lean_dec(v_mid_4259_);
v___y_4246_ = v___x_4265_;
goto v___jp_4245_;
}
}
v___jp_4266_:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; 
v___x_4268_ = lean_array_fget_borrowed(v___y_4267_, v_hi_4244_);
v___x_4269_ = lean_array_fget_borrowed(v___y_4267_, v_lo_4243_);
v___x_4270_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0(v___x_4268_, v___x_4269_);
if (v___x_4270_ == 0)
{
v___y_4261_ = v___y_4267_;
goto v___jp_4260_;
}
else
{
lean_object* v___x_4271_; 
v___x_4271_ = lean_array_fswap(v___y_4267_, v_lo_4243_, v_hi_4244_);
v___y_4261_ = v___x_4271_;
goto v___jp_4260_;
}
}
}
v___jp_4245_:
{
lean_object* v_pivot_4247_; lean_object* v___x_4248_; lean_object* v_fst_4249_; lean_object* v_snd_4250_; uint8_t v___x_4251_; 
v_pivot_4247_ = lean_array_fget(v___y_4246_, v_hi_4244_);
lean_inc_n(v_lo_4243_, 2);
v___x_4248_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___redArg(v_hi_4244_, v_pivot_4247_, v___y_4246_, v_lo_4243_, v_lo_4243_);
lean_dec(v_pivot_4247_);
v_fst_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc(v_fst_4249_);
v_snd_4250_ = lean_ctor_get(v___x_4248_, 1);
lean_inc(v_snd_4250_);
lean_dec_ref(v___x_4248_);
v___x_4251_ = lean_nat_dec_le(v_hi_4244_, v_fst_4249_);
if (v___x_4251_ == 0)
{
lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4252_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v_n_4241_, v_snd_4250_, v_lo_4243_, v_fst_4249_);
v___x_4253_ = lean_unsigned_to_nat(1u);
v___x_4254_ = lean_nat_add(v_fst_4249_, v___x_4253_);
lean_dec(v_fst_4249_);
v_as_4242_ = v___x_4252_;
v_lo_4243_ = v___x_4254_;
goto _start;
}
else
{
lean_dec(v_fst_4249_);
lean_dec(v_lo_4243_);
return v_snd_4250_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___boxed(lean_object* v_n_4276_, lean_object* v_as_4277_, lean_object* v_lo_4278_, lean_object* v_hi_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v_n_4276_, v_as_4277_, v_lo_4278_, v_hi_4279_);
lean_dec(v_hi_4279_);
lean_dec(v_n_4276_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___redArg(lean_object* v_hi_4281_, lean_object* v_pivot_4282_, lean_object* v_as_4283_, lean_object* v_i_4284_, lean_object* v_k_4285_){
_start:
{
uint8_t v___x_4286_; 
v___x_4286_ = lean_nat_dec_lt(v_k_4285_, v_hi_4281_);
if (v___x_4286_ == 0)
{
lean_object* v___x_4287_; lean_object* v___x_4288_; 
lean_dec(v_k_4285_);
v___x_4287_ = lean_array_fswap(v_as_4283_, v_i_4284_, v_hi_4281_);
v___x_4288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4288_, 0, v_i_4284_);
lean_ctor_set(v___x_4288_, 1, v___x_4287_);
return v___x_4288_;
}
else
{
lean_object* v___x_4289_; lean_object* v_fst_4290_; lean_object* v_fst_4291_; uint8_t v___x_4292_; 
v___x_4289_ = lean_array_fget_borrowed(v_as_4283_, v_k_4285_);
v_fst_4290_ = lean_ctor_get(v___x_4289_, 0);
v_fst_4291_ = lean_ctor_get(v_pivot_4282_, 0);
v___x_4292_ = lean_nat_dec_lt(v_fst_4290_, v_fst_4291_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4293_ = lean_unsigned_to_nat(1u);
v___x_4294_ = lean_nat_add(v_k_4285_, v___x_4293_);
lean_dec(v_k_4285_);
v_k_4285_ = v___x_4294_;
goto _start;
}
else
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4296_ = lean_array_fswap(v_as_4283_, v_i_4284_, v_k_4285_);
v___x_4297_ = lean_unsigned_to_nat(1u);
v___x_4298_ = lean_nat_add(v_i_4284_, v___x_4297_);
lean_dec(v_i_4284_);
v___x_4299_ = lean_nat_add(v_k_4285_, v___x_4297_);
lean_dec(v_k_4285_);
v_as_4283_ = v___x_4296_;
v_i_4284_ = v___x_4298_;
v_k_4285_ = v___x_4299_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___redArg___boxed(lean_object* v_hi_4301_, lean_object* v_pivot_4302_, lean_object* v_as_4303_, lean_object* v_i_4304_, lean_object* v_k_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___redArg(v_hi_4301_, v_pivot_4302_, v_as_4303_, v_i_4304_, v_k_4305_);
lean_dec_ref(v_pivot_4302_);
lean_dec(v_hi_4301_);
return v_res_4306_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0(lean_object* v_x1_4307_, lean_object* v_x2_4308_){
_start:
{
lean_object* v_fst_4309_; lean_object* v_fst_4310_; uint8_t v___x_4311_; 
v_fst_4309_ = lean_ctor_get(v_x1_4307_, 0);
v_fst_4310_ = lean_ctor_get(v_x2_4308_, 0);
v___x_4311_ = lean_nat_dec_lt(v_fst_4309_, v_fst_4310_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0___boxed(lean_object* v_x1_4312_, lean_object* v_x2_4313_){
_start:
{
uint8_t v_res_4314_; lean_object* v_r_4315_; 
v_res_4314_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0(v_x1_4312_, v_x2_4313_);
lean_dec_ref(v_x2_4313_);
lean_dec_ref(v_x1_4312_);
v_r_4315_ = lean_box(v_res_4314_);
return v_r_4315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg(lean_object* v_n_4316_, lean_object* v_as_4317_, lean_object* v_lo_4318_, lean_object* v_hi_4319_){
_start:
{
lean_object* v___y_4321_; uint8_t v___x_4331_; 
v___x_4331_ = lean_nat_dec_lt(v_lo_4318_, v_hi_4319_);
if (v___x_4331_ == 0)
{
lean_dec(v_lo_4318_);
return v_as_4317_;
}
else
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v_mid_4334_; lean_object* v___y_4336_; lean_object* v___y_4342_; lean_object* v___x_4347_; lean_object* v___x_4348_; uint8_t v___x_4349_; 
v___x_4332_ = lean_nat_add(v_lo_4318_, v_hi_4319_);
v___x_4333_ = lean_unsigned_to_nat(1u);
v_mid_4334_ = lean_nat_shiftr(v___x_4332_, v___x_4333_);
lean_dec(v___x_4332_);
v___x_4347_ = lean_array_fget_borrowed(v_as_4317_, v_mid_4334_);
v___x_4348_ = lean_array_fget_borrowed(v_as_4317_, v_lo_4318_);
v___x_4349_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0(v___x_4347_, v___x_4348_);
if (v___x_4349_ == 0)
{
v___y_4342_ = v_as_4317_;
goto v___jp_4341_;
}
else
{
lean_object* v___x_4350_; 
v___x_4350_ = lean_array_fswap(v_as_4317_, v_lo_4318_, v_mid_4334_);
v___y_4342_ = v___x_4350_;
goto v___jp_4341_;
}
v___jp_4335_:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v___x_4337_ = lean_array_fget_borrowed(v___y_4336_, v_mid_4334_);
v___x_4338_ = lean_array_fget_borrowed(v___y_4336_, v_hi_4319_);
v___x_4339_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0(v___x_4337_, v___x_4338_);
if (v___x_4339_ == 0)
{
lean_dec(v_mid_4334_);
v___y_4321_ = v___y_4336_;
goto v___jp_4320_;
}
else
{
lean_object* v___x_4340_; 
v___x_4340_ = lean_array_fswap(v___y_4336_, v_mid_4334_, v_hi_4319_);
lean_dec(v_mid_4334_);
v___y_4321_ = v___x_4340_;
goto v___jp_4320_;
}
}
v___jp_4341_:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; uint8_t v___x_4345_; 
v___x_4343_ = lean_array_fget_borrowed(v___y_4342_, v_hi_4319_);
v___x_4344_ = lean_array_fget_borrowed(v___y_4342_, v_lo_4318_);
v___x_4345_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0(v___x_4343_, v___x_4344_);
if (v___x_4345_ == 0)
{
v___y_4336_ = v___y_4342_;
goto v___jp_4335_;
}
else
{
lean_object* v___x_4346_; 
v___x_4346_ = lean_array_fswap(v___y_4342_, v_lo_4318_, v_hi_4319_);
v___y_4336_ = v___x_4346_;
goto v___jp_4335_;
}
}
}
v___jp_4320_:
{
lean_object* v_pivot_4322_; lean_object* v___x_4323_; lean_object* v_fst_4324_; lean_object* v_snd_4325_; uint8_t v___x_4326_; 
v_pivot_4322_ = lean_array_fget(v___y_4321_, v_hi_4319_);
lean_inc_n(v_lo_4318_, 2);
v___x_4323_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___redArg(v_hi_4319_, v_pivot_4322_, v___y_4321_, v_lo_4318_, v_lo_4318_);
lean_dec(v_pivot_4322_);
v_fst_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_fst_4324_);
v_snd_4325_ = lean_ctor_get(v___x_4323_, 1);
lean_inc(v_snd_4325_);
lean_dec_ref(v___x_4323_);
v___x_4326_ = lean_nat_dec_le(v_hi_4319_, v_fst_4324_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4327_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg(v_n_4316_, v_snd_4325_, v_lo_4318_, v_fst_4324_);
v___x_4328_ = lean_unsigned_to_nat(1u);
v___x_4329_ = lean_nat_add(v_fst_4324_, v___x_4328_);
lean_dec(v_fst_4324_);
v_as_4317_ = v___x_4327_;
v_lo_4318_ = v___x_4329_;
goto _start;
}
else
{
lean_dec(v_fst_4324_);
lean_dec(v_lo_4318_);
return v_snd_4325_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___boxed(lean_object* v_n_4351_, lean_object* v_as_4352_, lean_object* v_lo_4353_, lean_object* v_hi_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg(v_n_4351_, v_as_4352_, v_lo_4353_, v_hi_4354_);
lean_dec(v_hi_4354_);
lean_dec(v_n_4351_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__4(size_t v_sz_4356_, size_t v_i_4357_, lean_object* v_bs_4358_){
_start:
{
uint8_t v___x_4359_; 
v___x_4359_ = lean_usize_dec_lt(v_i_4357_, v_sz_4356_);
if (v___x_4359_ == 0)
{
return v_bs_4358_;
}
else
{
lean_object* v_v_4360_; lean_object* v___x_4361_; lean_object* v_bs_x27_4362_; size_t v___x_4363_; size_t v___x_4364_; lean_object* v___x_4365_; 
v_v_4360_ = lean_array_uget(v_bs_4358_, v_i_4357_);
v___x_4361_ = lean_unsigned_to_nat(0u);
v_bs_x27_4362_ = lean_array_uset(v_bs_4358_, v_i_4357_, v___x_4361_);
v___x_4363_ = ((size_t)1ULL);
v___x_4364_ = lean_usize_add(v_i_4357_, v___x_4363_);
v___x_4365_ = lean_array_uset(v_bs_x27_4362_, v_i_4357_, v_v_4360_);
v_i_4357_ = v___x_4364_;
v_bs_4358_ = v___x_4365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__4___boxed(lean_object* v_sz_4367_, lean_object* v_i_4368_, lean_object* v_bs_4369_){
_start:
{
size_t v_sz_boxed_4370_; size_t v_i_boxed_4371_; lean_object* v_res_4372_; 
v_sz_boxed_4370_ = lean_unbox_usize(v_sz_4367_);
lean_dec(v_sz_4367_);
v_i_boxed_4371_ = lean_unbox_usize(v_i_4368_);
lean_dec(v_i_4368_);
v_res_4372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__4(v_sz_boxed_4370_, v_i_boxed_4371_, v_bs_4369_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__5(lean_object* v_a_4373_, lean_object* v_a_4374_){
_start:
{
if (lean_obj_tag(v_a_4373_) == 0)
{
lean_object* v___x_4375_; 
v___x_4375_ = l_List_reverse___redArg(v_a_4374_);
return v___x_4375_;
}
else
{
lean_object* v_head_4376_; lean_object* v_tail_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4388_; 
v_head_4376_ = lean_ctor_get(v_a_4373_, 0);
v_tail_4377_ = lean_ctor_get(v_a_4373_, 1);
v_isSharedCheck_4388_ = !lean_is_exclusive(v_a_4373_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4379_ = v_a_4373_;
v_isShared_4380_ = v_isSharedCheck_4388_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_tail_4377_);
lean_inc(v_head_4376_);
lean_dec(v_a_4373_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4388_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4385_; 
v___x_4381_ = l_Nat_reprFast(v_head_4376_);
v___x_4382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4381_);
v___x_4383_ = l_Lean_MessageData_ofFormat(v___x_4382_);
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 1, v_a_4374_);
lean_ctor_set(v___x_4379_, 0, v___x_4383_);
v___x_4385_ = v___x_4379_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4383_);
lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_a_4374_);
v___x_4385_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
v_a_4373_ = v_tail_4377_;
v_a_4374_ = v___x_4385_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__1(void){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__0));
v___x_4391_ = l_Lean_stringToMessageData(v___x_4390_);
return v___x_4391_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3(void){
_start:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__2));
v___x_4394_ = l_Lean_stringToMessageData(v___x_4393_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10(lean_object* v_as_4395_, size_t v_sz_4396_, size_t v_i_4397_, lean_object* v_b_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v_a_4405_; uint8_t v___x_4409_; 
v___x_4409_ = lean_usize_dec_lt(v_i_4397_, v_sz_4396_);
if (v___x_4409_ == 0)
{
lean_object* v___x_4410_; 
v___x_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4410_, 0, v_b_4398_);
return v___x_4410_;
}
else
{
lean_object* v_toCold_4411_; lean_object* v_options_4412_; lean_object* v_inheritedTraceOptions_4413_; uint8_t v_hasTrace_4414_; lean_object* v___x_4415_; 
v_toCold_4411_ = lean_ctor_get(v___y_4401_, 0);
v_options_4412_ = lean_ctor_get(v_toCold_4411_, 2);
v_inheritedTraceOptions_4413_ = lean_ctor_get(v_toCold_4411_, 11);
v_hasTrace_4414_ = lean_ctor_get_uint8(v_options_4412_, sizeof(void*)*1);
v___x_4415_ = lean_box(0);
if (v_hasTrace_4414_ == 0)
{
v_a_4405_ = v___x_4415_;
goto v___jp_4404_;
}
else
{
lean_object* v_cls_4416_; lean_object* v___x_4417_; uint8_t v___x_4418_; 
v_cls_4416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_4417_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9);
v___x_4418_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4413_, v_options_4412_, v___x_4417_);
if (v___x_4418_ == 0)
{
v_a_4405_ = v___x_4415_;
goto v___jp_4404_;
}
else
{
lean_object* v_a_4419_; lean_object* v_hyp_4420_; lean_object* v_boundSorts_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4442_; 
v_a_4419_ = lean_array_uget(v_as_4395_, v_i_4397_);
v_hyp_4420_ = lean_ctor_get(v_a_4419_, 0);
v_boundSorts_4421_ = lean_ctor_get(v_a_4419_, 1);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_a_4419_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4423_ = v_a_4419_;
v_isShared_4424_ = v_isSharedCheck_4442_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_boundSorts_4421_);
lean_inc(v_hyp_4420_);
lean_dec(v_a_4419_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4442_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v_type_4425_; size_t v_sz_4426_; lean_object* v___x_4427_; size_t v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4435_; 
v_type_4425_ = lean_ctor_get(v_hyp_4420_, 1);
lean_inc_ref(v_type_4425_);
lean_dec_ref(v_hyp_4420_);
v_sz_4426_ = lean_array_size(v_boundSorts_4421_);
v___x_4427_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__1);
v___x_4428_ = ((size_t)0ULL);
v___x_4429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__4(v_sz_4426_, v___x_4428_, v_boundSorts_4421_);
v___x_4430_ = lean_array_to_list(v___x_4429_);
v___x_4431_ = lean_box(0);
v___x_4432_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__5(v___x_4430_, v___x_4431_);
v___x_4433_ = l_Lean_MessageData_ofList(v___x_4432_);
if (v_isShared_4424_ == 0)
{
lean_ctor_set_tag(v___x_4423_, 7);
lean_ctor_set(v___x_4423_, 1, v___x_4433_);
lean_ctor_set(v___x_4423_, 0, v___x_4427_);
v___x_4435_ = v___x_4423_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4427_);
lean_ctor_set(v_reuseFailAlloc_4441_, 1, v___x_4433_);
v___x_4435_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4436_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3);
v___x_4437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4435_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
v___x_4438_ = l_Lean_MessageData_ofExpr(v_type_4425_);
v___x_4439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4439_, 0, v___x_4437_);
lean_ctor_set(v___x_4439_, 1, v___x_4438_);
v___x_4440_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3(v_cls_4416_, v___x_4439_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_dec_ref_known(v___x_4440_, 1);
v_a_4405_ = v___x_4415_;
goto v___jp_4404_;
}
else
{
return v___x_4440_;
}
}
}
}
}
}
v___jp_4404_:
{
size_t v___x_4406_; size_t v___x_4407_; 
v___x_4406_ = ((size_t)1ULL);
v___x_4407_ = lean_usize_add(v_i_4397_, v___x_4406_);
v_i_4397_ = v___x_4407_;
v_b_4398_ = v_a_4405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___boxed(lean_object* v_as_4443_, lean_object* v_sz_4444_, lean_object* v_i_4445_, lean_object* v_b_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
size_t v_sz_boxed_4452_; size_t v_i_boxed_4453_; lean_object* v_res_4454_; 
v_sz_boxed_4452_ = lean_unbox_usize(v_sz_4444_);
lean_dec(v_sz_4444_);
v_i_boxed_4453_ = lean_unbox_usize(v_i_4445_);
lean_dec(v_i_4445_);
v_res_4454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10(v_as_4443_, v_sz_boxed_4452_, v_i_boxed_4453_, v_b_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec_ref(v_as_4443_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__6(lean_object* v_a_4455_, lean_object* v_a_4456_){
_start:
{
if (lean_obj_tag(v_a_4455_) == 0)
{
lean_object* v___x_4457_; 
v___x_4457_ = l_List_reverse___redArg(v_a_4456_);
return v___x_4457_;
}
else
{
lean_object* v_head_4458_; lean_object* v_tail_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4468_; 
v_head_4458_ = lean_ctor_get(v_a_4455_, 0);
v_tail_4459_ = lean_ctor_get(v_a_4455_, 1);
v_isSharedCheck_4468_ = !lean_is_exclusive(v_a_4455_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4461_ = v_a_4455_;
v_isShared_4462_ = v_isSharedCheck_4468_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_tail_4459_);
lean_inc(v_head_4458_);
lean_dec(v_a_4455_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4468_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4463_; lean_object* v___x_4465_; 
v___x_4463_ = l_Lean_MessageData_ofExpr(v_head_4458_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 1, v_a_4456_);
lean_ctor_set(v___x_4461_, 0, v___x_4463_);
v___x_4465_ = v___x_4461_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4463_);
lean_ctor_set(v_reuseFailAlloc_4467_, 1, v_a_4456_);
v___x_4465_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
v_a_4455_ = v_tail_4459_;
v_a_4456_ = v___x_4465_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__1(void){
_start:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__0));
v___x_4471_ = l_Lean_stringToMessageData(v___x_4470_);
return v___x_4471_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__3(void){
_start:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__2));
v___x_4474_ = l_Lean_stringToMessageData(v___x_4473_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7(lean_object* v_as_4475_, size_t v_sz_4476_, size_t v_i_4477_, lean_object* v_b_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v_a_4485_; uint8_t v___x_4489_; 
v___x_4489_ = lean_usize_dec_lt(v_i_4477_, v_sz_4476_);
if (v___x_4489_ == 0)
{
lean_object* v___x_4490_; 
v___x_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4490_, 0, v_b_4478_);
return v___x_4490_;
}
else
{
lean_object* v_a_4491_; lean_object* v_toCold_4492_; lean_object* v_options_4493_; lean_object* v_fst_4494_; lean_object* v_snd_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4526_; 
v_a_4491_ = lean_array_uget(v_as_4475_, v_i_4477_);
v_toCold_4492_ = lean_ctor_get(v___y_4481_, 0);
v_options_4493_ = lean_ctor_get(v_toCold_4492_, 2);
v_fst_4494_ = lean_ctor_get(v_a_4491_, 0);
v_snd_4495_ = lean_ctor_get(v_a_4491_, 1);
v_isSharedCheck_4526_ = !lean_is_exclusive(v_a_4491_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4497_ = v_a_4491_;
v_isShared_4498_ = v_isSharedCheck_4526_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_snd_4495_);
lean_inc(v_fst_4494_);
lean_dec(v_a_4491_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4526_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v_inheritedTraceOptions_4499_; uint8_t v_hasTrace_4500_; lean_object* v___x_4501_; 
v_inheritedTraceOptions_4499_ = lean_ctor_get(v_toCold_4492_, 11);
v_hasTrace_4500_ = lean_ctor_get_uint8(v_options_4493_, sizeof(void*)*1);
v___x_4501_ = lean_box(0);
if (v_hasTrace_4500_ == 0)
{
lean_del_object(v___x_4497_);
lean_dec(v_snd_4495_);
lean_dec(v_fst_4494_);
v_a_4485_ = v___x_4501_;
goto v___jp_4484_;
}
else
{
lean_object* v_cls_4502_; lean_object* v___x_4503_; uint8_t v___x_4504_; 
v_cls_4502_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_4503_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9);
v___x_4504_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4499_, v_options_4493_, v___x_4503_);
if (v___x_4504_ == 0)
{
lean_del_object(v___x_4497_);
lean_dec(v_snd_4495_);
lean_dec(v_fst_4494_);
v_a_4485_ = v___x_4501_;
goto v___jp_4484_;
}
else
{
lean_object* v_type_4505_; lean_object* v_elements_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4512_; 
v_type_4505_ = lean_ctor_get(v_snd_4495_, 0);
lean_inc_ref(v_type_4505_);
v_elements_4506_ = lean_ctor_get(v_snd_4495_, 2);
lean_inc_ref(v_elements_4506_);
lean_dec(v_snd_4495_);
v___x_4507_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__1);
v___x_4508_ = l_Nat_reprFast(v_fst_4494_);
v___x_4509_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4508_);
v___x_4510_ = l_Lean_MessageData_ofFormat(v___x_4509_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set_tag(v___x_4497_, 7);
lean_ctor_set(v___x_4497_, 1, v___x_4510_);
lean_ctor_set(v___x_4497_, 0, v___x_4507_);
v___x_4512_ = v___x_4497_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4507_);
lean_ctor_set(v_reuseFailAlloc_4525_, 1, v___x_4510_);
v___x_4512_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4513_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3);
v___x_4514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4514_, 0, v___x_4512_);
lean_ctor_set(v___x_4514_, 1, v___x_4513_);
v___x_4515_ = l_Lean_MessageData_ofExpr(v_type_4505_);
v___x_4516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4514_);
lean_ctor_set(v___x_4516_, 1, v___x_4515_);
v___x_4517_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__3);
v___x_4518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4516_);
lean_ctor_set(v___x_4518_, 1, v___x_4517_);
v___x_4519_ = lean_array_to_list(v_elements_4506_);
v___x_4520_ = lean_box(0);
v___x_4521_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__6(v___x_4519_, v___x_4520_);
v___x_4522_ = l_Lean_MessageData_ofList(v___x_4521_);
v___x_4523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4518_);
lean_ctor_set(v___x_4523_, 1, v___x_4522_);
v___x_4524_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3(v_cls_4502_, v___x_4523_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_dec_ref_known(v___x_4524_, 1);
v_a_4485_ = v___x_4501_;
goto v___jp_4484_;
}
else
{
return v___x_4524_;
}
}
}
}
}
}
v___jp_4484_:
{
size_t v___x_4486_; size_t v___x_4487_; 
v___x_4486_ = ((size_t)1ULL);
v___x_4487_ = lean_usize_add(v_i_4477_, v___x_4486_);
v_i_4477_ = v___x_4487_;
v_b_4478_ = v_a_4485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___boxed(lean_object* v_as_4527_, lean_object* v_sz_4528_, lean_object* v_i_4529_, lean_object* v_b_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
size_t v_sz_boxed_4536_; size_t v_i_boxed_4537_; lean_object* v_res_4538_; 
v_sz_boxed_4536_ = lean_unbox_usize(v_sz_4528_);
lean_dec(v_sz_4528_);
v_i_boxed_4537_ = lean_unbox_usize(v_i_4529_);
lean_dec(v_i_4529_);
v_res_4538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7(v_as_4527_, v_sz_boxed_4536_, v_i_boxed_4537_, v_b_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec_ref(v_as_4527_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__18(lean_object* v_x_4539_, lean_object* v_x_4540_){
_start:
{
if (lean_obj_tag(v_x_4540_) == 0)
{
return v_x_4539_;
}
else
{
lean_object* v_key_4541_; lean_object* v_value_4542_; lean_object* v_tail_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
v_key_4541_ = lean_ctor_get(v_x_4540_, 0);
v_value_4542_ = lean_ctor_get(v_x_4540_, 1);
v_tail_4543_ = lean_ctor_get(v_x_4540_, 2);
lean_inc(v_value_4542_);
lean_inc(v_key_4541_);
v___x_4544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4544_, 0, v_key_4541_);
lean_ctor_set(v___x_4544_, 1, v_value_4542_);
v___x_4545_ = lean_array_push(v_x_4539_, v___x_4544_);
v_x_4539_ = v___x_4545_;
v_x_4540_ = v_tail_4543_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__18___boxed(lean_object* v_x_4547_, lean_object* v_x_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__18(v_x_4547_, v_x_4548_);
lean_dec(v_x_4548_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__19(lean_object* v_as_4550_, size_t v_i_4551_, size_t v_stop_4552_, lean_object* v_b_4553_){
_start:
{
uint8_t v___x_4554_; 
v___x_4554_ = lean_usize_dec_eq(v_i_4551_, v_stop_4552_);
if (v___x_4554_ == 0)
{
lean_object* v___x_4555_; lean_object* v___x_4556_; size_t v___x_4557_; size_t v___x_4558_; 
v___x_4555_ = lean_array_uget_borrowed(v_as_4550_, v_i_4551_);
v___x_4556_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__18(v_b_4553_, v___x_4555_);
v___x_4557_ = ((size_t)1ULL);
v___x_4558_ = lean_usize_add(v_i_4551_, v___x_4557_);
v_i_4551_ = v___x_4558_;
v_b_4553_ = v___x_4556_;
goto _start;
}
else
{
return v_b_4553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__19___boxed(lean_object* v_as_4560_, lean_object* v_i_4561_, lean_object* v_stop_4562_, lean_object* v_b_4563_){
_start:
{
size_t v_i_boxed_4564_; size_t v_stop_boxed_4565_; lean_object* v_res_4566_; 
v_i_boxed_4564_ = lean_unbox_usize(v_i_4561_);
lean_dec(v_i_4561_);
v_stop_boxed_4565_ = lean_unbox_usize(v_stop_4562_);
lean_dec(v_stop_4562_);
v_res_4566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__19(v_as_4560_, v_i_boxed_4564_, v_stop_boxed_4565_, v_b_4563_);
lean_dec_ref(v_as_4560_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__21(lean_object* v_opts_4567_, lean_object* v_opt_4568_){
_start:
{
lean_object* v_name_4569_; lean_object* v_defValue_4570_; lean_object* v_map_4571_; lean_object* v___x_4572_; 
v_name_4569_ = lean_ctor_get(v_opt_4568_, 0);
v_defValue_4570_ = lean_ctor_get(v_opt_4568_, 1);
v_map_4571_ = lean_ctor_get(v_opts_4567_, 0);
v___x_4572_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4571_, v_name_4569_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_inc(v_defValue_4570_);
return v_defValue_4570_;
}
else
{
lean_object* v_val_4573_; 
v_val_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_val_4573_);
lean_dec_ref_known(v___x_4572_, 1);
if (lean_obj_tag(v_val_4573_) == 3)
{
lean_object* v_v_4574_; 
v_v_4574_ = lean_ctor_get(v_val_4573_, 0);
lean_inc(v_v_4574_);
lean_dec_ref_known(v_val_4573_, 1);
return v_v_4574_;
}
else
{
lean_dec(v_val_4573_);
lean_inc(v_defValue_4570_);
return v_defValue_4570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__21___boxed(lean_object* v_opts_4575_, lean_object* v_opt_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__21(v_opts_4575_, v_opt_4576_);
lean_dec_ref(v_opt_4576_);
lean_dec_ref(v_opts_4575_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg(lean_object* v_x_4578_){
_start:
{
if (lean_obj_tag(v_x_4578_) == 0)
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4587_; 
v_a_4580_ = lean_ctor_get(v_x_4578_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_x_4578_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4582_ = v_x_4578_;
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v_x_4578_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4585_; 
if (v_isShared_4583_ == 0)
{
lean_ctor_set_tag(v___x_4582_, 1);
v___x_4585_ = v___x_4582_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
else
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4595_; 
v_a_4588_ = lean_ctor_get(v_x_4578_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v_x_4578_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4590_ = v_x_4578_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v_x_4578_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4593_; 
if (v_isShared_4591_ == 0)
{
lean_ctor_set_tag(v___x_4590_, 0);
v___x_4593_ = v___x_4590_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg___boxed(lean_object* v_x_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg(v_x_4596_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18_spec__20(size_t v_sz_4599_, size_t v_i_4600_, lean_object* v_bs_4601_){
_start:
{
uint8_t v___x_4602_; 
v___x_4602_ = lean_usize_dec_lt(v_i_4600_, v_sz_4599_);
if (v___x_4602_ == 0)
{
return v_bs_4601_;
}
else
{
lean_object* v_v_4603_; lean_object* v_msg_4604_; lean_object* v___x_4605_; lean_object* v_bs_x27_4606_; size_t v___x_4607_; size_t v___x_4608_; lean_object* v___x_4609_; 
v_v_4603_ = lean_array_uget_borrowed(v_bs_4601_, v_i_4600_);
v_msg_4604_ = lean_ctor_get(v_v_4603_, 1);
lean_inc_ref(v_msg_4604_);
v___x_4605_ = lean_unsigned_to_nat(0u);
v_bs_x27_4606_ = lean_array_uset(v_bs_4601_, v_i_4600_, v___x_4605_);
v___x_4607_ = ((size_t)1ULL);
v___x_4608_ = lean_usize_add(v_i_4600_, v___x_4607_);
v___x_4609_ = lean_array_uset(v_bs_x27_4606_, v_i_4600_, v_msg_4604_);
v_i_4600_ = v___x_4608_;
v_bs_4601_ = v___x_4609_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18_spec__20___boxed(lean_object* v_sz_4611_, lean_object* v_i_4612_, lean_object* v_bs_4613_){
_start:
{
size_t v_sz_boxed_4614_; size_t v_i_boxed_4615_; lean_object* v_res_4616_; 
v_sz_boxed_4614_ = lean_unbox_usize(v_sz_4611_);
lean_dec(v_sz_4611_);
v_i_boxed_4615_ = lean_unbox_usize(v_i_4612_);
lean_dec(v_i_4612_);
v_res_4616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18_spec__20(v_sz_boxed_4614_, v_i_boxed_4615_, v_bs_4613_);
return v_res_4616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18(lean_object* v_oldTraces_4617_, lean_object* v_data_4618_, lean_object* v_ref_4619_, lean_object* v_msg_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v_toCold_4626_; lean_object* v_currRecDepth_4627_; lean_object* v_ref_4628_; uint16_t v_optionFlags_4629_; uint8_t v_suppressElabErrors_4630_; uint8_t v_checkDeprecated_4631_; uint8_t v_isRecordingDeps_4632_; lean_object* v_ref_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v_traceState_4636_; lean_object* v_traces_4637_; lean_object* v___x_4638_; size_t v_sz_4639_; size_t v___x_4640_; lean_object* v___x_4641_; lean_object* v_msg_4642_; lean_object* v___x_4643_; lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4682_; 
v_toCold_4626_ = lean_ctor_get(v___y_4623_, 0);
v_currRecDepth_4627_ = lean_ctor_get(v___y_4623_, 1);
v_ref_4628_ = lean_ctor_get(v___y_4623_, 2);
v_optionFlags_4629_ = lean_ctor_get_uint16(v___y_4623_, sizeof(void*)*3);
v_suppressElabErrors_4630_ = lean_ctor_get_uint8(v___y_4623_, sizeof(void*)*3 + 2);
v_checkDeprecated_4631_ = lean_ctor_get_uint8(v___y_4623_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4632_ = lean_ctor_get_uint8(v___y_4623_, sizeof(void*)*3 + 4);
v_ref_4633_ = l_Lean_replaceRef(v_ref_4619_, v_ref_4628_);
lean_inc(v_currRecDepth_4627_);
lean_inc_ref(v_toCold_4626_);
v___x_4634_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4634_, 0, v_toCold_4626_);
lean_ctor_set(v___x_4634_, 1, v_currRecDepth_4627_);
lean_ctor_set(v___x_4634_, 2, v_ref_4633_);
lean_ctor_set_uint16(v___x_4634_, sizeof(void*)*3, v_optionFlags_4629_);
lean_ctor_set_uint8(v___x_4634_, sizeof(void*)*3 + 2, v_suppressElabErrors_4630_);
lean_ctor_set_uint8(v___x_4634_, sizeof(void*)*3 + 3, v_checkDeprecated_4631_);
lean_ctor_set_uint8(v___x_4634_, sizeof(void*)*3 + 4, v_isRecordingDeps_4632_);
v___x_4635_ = lean_st_ref_get(v___y_4624_);
v_traceState_4636_ = lean_ctor_get(v___x_4635_, 4);
lean_inc_ref(v_traceState_4636_);
lean_dec(v___x_4635_);
v_traces_4637_ = lean_ctor_get(v_traceState_4636_, 0);
lean_inc_ref(v_traces_4637_);
lean_dec_ref(v_traceState_4636_);
v___x_4638_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4637_);
lean_dec_ref(v_traces_4637_);
v_sz_4639_ = lean_array_size(v___x_4638_);
v___x_4640_ = ((size_t)0ULL);
v___x_4641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18_spec__20(v_sz_4639_, v___x_4640_, v___x_4638_);
v_msg_4642_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4642_, 0, v_data_4618_);
lean_ctor_set(v_msg_4642_, 1, v_msg_4620_);
lean_ctor_set(v_msg_4642_, 2, v___x_4641_);
v___x_4643_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2_spec__3(v_msg_4642_, v___y_4621_, v___y_4622_, v___x_4634_, v___y_4624_);
lean_dec_ref_known(v___x_4634_, 3);
v_a_4644_ = lean_ctor_get(v___x_4643_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4646_ = v___x_4643_;
v_isShared_4647_ = v_isSharedCheck_4682_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4643_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4682_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4648_; lean_object* v_traceState_4649_; lean_object* v_env_4650_; lean_object* v_nextMacroScope_4651_; lean_object* v_ngen_4652_; lean_object* v_auxDeclNGen_4653_; lean_object* v_cache_4654_; lean_object* v_recordedDeps_4655_; lean_object* v_messages_4656_; lean_object* v_infoState_4657_; lean_object* v_snapshotTasks_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4681_; 
v___x_4648_ = lean_st_ref_take(v___y_4624_);
v_traceState_4649_ = lean_ctor_get(v___x_4648_, 4);
v_env_4650_ = lean_ctor_get(v___x_4648_, 0);
v_nextMacroScope_4651_ = lean_ctor_get(v___x_4648_, 1);
v_ngen_4652_ = lean_ctor_get(v___x_4648_, 2);
v_auxDeclNGen_4653_ = lean_ctor_get(v___x_4648_, 3);
v_cache_4654_ = lean_ctor_get(v___x_4648_, 5);
v_recordedDeps_4655_ = lean_ctor_get(v___x_4648_, 6);
v_messages_4656_ = lean_ctor_get(v___x_4648_, 7);
v_infoState_4657_ = lean_ctor_get(v___x_4648_, 8);
v_snapshotTasks_4658_ = lean_ctor_get(v___x_4648_, 9);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4660_ = v___x_4648_;
v_isShared_4661_ = v_isSharedCheck_4681_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_snapshotTasks_4658_);
lean_inc(v_infoState_4657_);
lean_inc(v_messages_4656_);
lean_inc(v_recordedDeps_4655_);
lean_inc(v_cache_4654_);
lean_inc(v_traceState_4649_);
lean_inc(v_auxDeclNGen_4653_);
lean_inc(v_ngen_4652_);
lean_inc(v_nextMacroScope_4651_);
lean_inc(v_env_4650_);
lean_dec(v___x_4648_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4681_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
uint64_t v_tid_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4679_; 
v_tid_4662_ = lean_ctor_get_uint64(v_traceState_4649_, sizeof(void*)*1);
v_isSharedCheck_4679_ = !lean_is_exclusive(v_traceState_4649_);
if (v_isSharedCheck_4679_ == 0)
{
lean_object* v_unused_4680_; 
v_unused_4680_ = lean_ctor_get(v_traceState_4649_, 0);
lean_dec(v_unused_4680_);
v___x_4664_ = v_traceState_4649_;
v_isShared_4665_ = v_isSharedCheck_4679_;
goto v_resetjp_4663_;
}
else
{
lean_dec(v_traceState_4649_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4679_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4670_; 
v___x_4666_ = lean_box(0);
v___x_4667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4667_, 0, v_ref_4619_);
lean_ctor_set(v___x_4667_, 1, v_a_4644_);
v___x_4668_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4617_, v___x_4667_);
if (v_isShared_4665_ == 0)
{
lean_ctor_set(v___x_4664_, 0, v___x_4668_);
v___x_4670_ = v___x_4664_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v___x_4668_);
lean_ctor_set_uint64(v_reuseFailAlloc_4678_, sizeof(void*)*1, v_tid_4662_);
v___x_4670_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
lean_object* v___x_4672_; 
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 4, v___x_4670_);
v___x_4672_ = v___x_4660_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_env_4650_);
lean_ctor_set(v_reuseFailAlloc_4677_, 1, v_nextMacroScope_4651_);
lean_ctor_set(v_reuseFailAlloc_4677_, 2, v_ngen_4652_);
lean_ctor_set(v_reuseFailAlloc_4677_, 3, v_auxDeclNGen_4653_);
lean_ctor_set(v_reuseFailAlloc_4677_, 4, v___x_4670_);
lean_ctor_set(v_reuseFailAlloc_4677_, 5, v_cache_4654_);
lean_ctor_set(v_reuseFailAlloc_4677_, 6, v_recordedDeps_4655_);
lean_ctor_set(v_reuseFailAlloc_4677_, 7, v_messages_4656_);
lean_ctor_set(v_reuseFailAlloc_4677_, 8, v_infoState_4657_);
lean_ctor_set(v_reuseFailAlloc_4677_, 9, v_snapshotTasks_4658_);
v___x_4672_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
lean_object* v___x_4673_; lean_object* v___x_4675_; 
v___x_4673_ = lean_st_ref_put(v___y_4624_, v___x_4672_);
if (v_isShared_4647_ == 0)
{
lean_ctor_set(v___x_4646_, 0, v___x_4666_);
v___x_4675_ = v___x_4646_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4666_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18___boxed(lean_object* v_oldTraces_4683_, lean_object* v_data_4684_, lean_object* v_ref_4685_, lean_object* v_msg_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18(v_oldTraces_4683_, v_data_4684_, v_ref_4685_, v_msg_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_);
lean_dec(v___y_4690_);
lean_dec_ref(v___y_4689_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
return v_res_4692_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__20(lean_object* v_e_4693_){
_start:
{
if (lean_obj_tag(v_e_4693_) == 0)
{
uint8_t v___x_4694_; 
v___x_4694_ = 2;
return v___x_4694_;
}
else
{
uint8_t v___x_4695_; 
v___x_4695_ = 0;
return v___x_4695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__20___boxed(lean_object* v_e_4696_){
_start:
{
uint8_t v_res_4697_; lean_object* v_r_4698_; 
v_res_4697_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__20(v_e_4696_);
lean_dec_ref(v_e_4696_);
v_r_4698_ = lean_box(v_res_4697_);
return v_r_4698_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__1(void){
_start:
{
lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4700_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__0));
v___x_4701_ = l_Lean_stringToMessageData(v___x_4700_);
return v___x_4701_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__2(void){
_start:
{
lean_object* v___x_4702_; double v___x_4703_; 
v___x_4702_ = lean_unsigned_to_nat(1000u);
v___x_4703_ = lean_float_of_nat(v___x_4702_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16(lean_object* v_cls_4704_, uint8_t v_collapsed_4705_, lean_object* v_tag_4706_, lean_object* v_opts_4707_, uint8_t v_clsEnabled_4708_, lean_object* v_oldTraces_4709_, lean_object* v_msg_4710_, lean_object* v_resStartStop_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
lean_object* v_fst_4717_; lean_object* v_snd_4718_; lean_object* v___y_4720_; lean_object* v___y_4721_; lean_object* v_data_4722_; lean_object* v_fst_4725_; lean_object* v_snd_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; lean_object* v___y_4730_; lean_object* v_a_4731_; uint8_t v___y_4746_; double v___y_4778_; 
v_fst_4717_ = lean_ctor_get(v_resStartStop_4711_, 0);
lean_inc(v_fst_4717_);
v_snd_4718_ = lean_ctor_get(v_resStartStop_4711_, 1);
lean_inc(v_snd_4718_);
lean_dec_ref(v_resStartStop_4711_);
v_fst_4725_ = lean_ctor_get(v_snd_4718_, 0);
lean_inc(v_fst_4725_);
v_snd_4726_ = lean_ctor_get(v_snd_4718_, 1);
lean_inc(v_snd_4726_);
lean_dec(v_snd_4718_);
v___x_4727_ = l_Lean_trace_profiler;
v___x_4728_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15(v_opts_4707_, v___x_4727_);
if (v___x_4728_ == 0)
{
v___y_4746_ = v___x_4728_;
goto v___jp_4745_;
}
else
{
lean_object* v___x_4783_; uint8_t v___x_4784_; 
v___x_4783_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4784_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15(v_opts_4707_, v___x_4783_);
if (v___x_4784_ == 0)
{
lean_object* v___x_4785_; lean_object* v___x_4786_; double v___x_4787_; double v___x_4788_; double v___x_4789_; 
v___x_4785_ = l_Lean_trace_profiler_threshold;
v___x_4786_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__21(v_opts_4707_, v___x_4785_);
v___x_4787_ = lean_float_of_nat(v___x_4786_);
v___x_4788_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__2);
v___x_4789_ = lean_float_div(v___x_4787_, v___x_4788_);
v___y_4778_ = v___x_4789_;
goto v___jp_4777_;
}
else
{
lean_object* v___x_4790_; lean_object* v___x_4791_; double v___x_4792_; 
v___x_4790_ = l_Lean_trace_profiler_threshold;
v___x_4791_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__21(v_opts_4707_, v___x_4790_);
v___x_4792_ = lean_float_of_nat(v___x_4791_);
v___y_4778_ = v___x_4792_;
goto v___jp_4777_;
}
}
v___jp_4719_:
{
lean_object* v___x_4723_; 
lean_inc(v___y_4721_);
v___x_4723_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18(v_oldTraces_4709_, v_data_4722_, v___y_4721_, v___y_4720_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v___x_4724_; 
lean_dec_ref_known(v___x_4723_, 1);
v___x_4724_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg(v_fst_4717_);
return v___x_4724_;
}
else
{
lean_dec(v_fst_4717_);
return v___x_4723_;
}
}
v___jp_4729_:
{
uint8_t v_result_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; double v___x_4735_; lean_object* v_data_4736_; 
v_result_4732_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__20(v_fst_4717_);
v___x_4733_ = lean_box(v_result_4732_);
v___x_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4733_);
v___x_4735_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_4706_);
lean_inc_ref(v___x_4734_);
lean_inc(v_cls_4704_);
v_data_4736_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4736_, 0, v_cls_4704_);
lean_ctor_set(v_data_4736_, 1, v___x_4734_);
lean_ctor_set(v_data_4736_, 2, v_tag_4706_);
lean_ctor_set_float(v_data_4736_, sizeof(void*)*3, v___x_4735_);
lean_ctor_set_float(v_data_4736_, sizeof(void*)*3 + 8, v___x_4735_);
lean_ctor_set_uint8(v_data_4736_, sizeof(void*)*3 + 16, v_collapsed_4705_);
if (v___x_4728_ == 0)
{
lean_dec_ref_known(v___x_4734_, 1);
lean_dec(v_snd_4726_);
lean_dec(v_fst_4725_);
lean_dec_ref(v_tag_4706_);
lean_dec(v_cls_4704_);
v___y_4720_ = v_a_4731_;
v___y_4721_ = v___y_4730_;
v_data_4722_ = v_data_4736_;
goto v___jp_4719_;
}
else
{
lean_object* v_data_4737_; double v___x_4738_; double v___x_4739_; 
lean_dec_ref_known(v_data_4736_, 3);
v_data_4737_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4737_, 0, v_cls_4704_);
lean_ctor_set(v_data_4737_, 1, v___x_4734_);
lean_ctor_set(v_data_4737_, 2, v_tag_4706_);
v___x_4738_ = lean_unbox_float(v_fst_4725_);
lean_dec(v_fst_4725_);
lean_ctor_set_float(v_data_4737_, sizeof(void*)*3, v___x_4738_);
v___x_4739_ = lean_unbox_float(v_snd_4726_);
lean_dec(v_snd_4726_);
lean_ctor_set_float(v_data_4737_, sizeof(void*)*3 + 8, v___x_4739_);
lean_ctor_set_uint8(v_data_4737_, sizeof(void*)*3 + 16, v_collapsed_4705_);
v___y_4720_ = v_a_4731_;
v___y_4721_ = v___y_4730_;
v_data_4722_ = v_data_4737_;
goto v___jp_4719_;
}
}
v___jp_4740_:
{
lean_object* v_ref_4741_; lean_object* v___x_4742_; 
v_ref_4741_ = lean_ctor_get(v___y_4714_, 2);
lean_inc(v___y_4715_);
lean_inc_ref(v___y_4714_);
lean_inc(v___y_4713_);
lean_inc_ref(v___y_4712_);
lean_inc(v_fst_4717_);
v___x_4742_ = lean_apply_6(v_msg_4710_, v_fst_4717_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, lean_box(0));
if (lean_obj_tag(v___x_4742_) == 0)
{
lean_object* v_a_4743_; 
v_a_4743_ = lean_ctor_get(v___x_4742_, 0);
lean_inc(v_a_4743_);
lean_dec_ref_known(v___x_4742_, 1);
v___y_4730_ = v_ref_4741_;
v_a_4731_ = v_a_4743_;
goto v___jp_4729_;
}
else
{
lean_object* v___x_4744_; 
lean_dec_ref_known(v___x_4742_, 1);
v___x_4744_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__1);
v___y_4730_ = v_ref_4741_;
v_a_4731_ = v___x_4744_;
goto v___jp_4729_;
}
}
v___jp_4745_:
{
if (v_clsEnabled_4708_ == 0)
{
if (v___y_4746_ == 0)
{
lean_object* v___x_4747_; lean_object* v_traceState_4748_; lean_object* v_env_4749_; lean_object* v_nextMacroScope_4750_; lean_object* v_ngen_4751_; lean_object* v_auxDeclNGen_4752_; lean_object* v_cache_4753_; lean_object* v_recordedDeps_4754_; lean_object* v_messages_4755_; lean_object* v_infoState_4756_; lean_object* v_snapshotTasks_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4776_; 
lean_dec(v_snd_4726_);
lean_dec(v_fst_4725_);
lean_dec_ref(v_msg_4710_);
lean_dec_ref(v_tag_4706_);
lean_dec(v_cls_4704_);
v___x_4747_ = lean_st_ref_take(v___y_4715_);
v_traceState_4748_ = lean_ctor_get(v___x_4747_, 4);
v_env_4749_ = lean_ctor_get(v___x_4747_, 0);
v_nextMacroScope_4750_ = lean_ctor_get(v___x_4747_, 1);
v_ngen_4751_ = lean_ctor_get(v___x_4747_, 2);
v_auxDeclNGen_4752_ = lean_ctor_get(v___x_4747_, 3);
v_cache_4753_ = lean_ctor_get(v___x_4747_, 5);
v_recordedDeps_4754_ = lean_ctor_get(v___x_4747_, 6);
v_messages_4755_ = lean_ctor_get(v___x_4747_, 7);
v_infoState_4756_ = lean_ctor_get(v___x_4747_, 8);
v_snapshotTasks_4757_ = lean_ctor_get(v___x_4747_, 9);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4759_ = v___x_4747_;
v_isShared_4760_ = v_isSharedCheck_4776_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_snapshotTasks_4757_);
lean_inc(v_infoState_4756_);
lean_inc(v_messages_4755_);
lean_inc(v_recordedDeps_4754_);
lean_inc(v_cache_4753_);
lean_inc(v_traceState_4748_);
lean_inc(v_auxDeclNGen_4752_);
lean_inc(v_ngen_4751_);
lean_inc(v_nextMacroScope_4750_);
lean_inc(v_env_4749_);
lean_dec(v___x_4747_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4776_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
uint64_t v_tid_4761_; lean_object* v_traces_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4775_; 
v_tid_4761_ = lean_ctor_get_uint64(v_traceState_4748_, sizeof(void*)*1);
v_traces_4762_ = lean_ctor_get(v_traceState_4748_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v_traceState_4748_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4764_ = v_traceState_4748_;
v_isShared_4765_ = v_isSharedCheck_4775_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_traces_4762_);
lean_dec(v_traceState_4748_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4775_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4766_; lean_object* v___x_4768_; 
v___x_4766_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4709_, v_traces_4762_);
lean_dec_ref(v_traces_4762_);
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 0, v___x_4766_);
v___x_4768_ = v___x_4764_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4766_);
lean_ctor_set_uint64(v_reuseFailAlloc_4774_, sizeof(void*)*1, v_tid_4761_);
v___x_4768_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
lean_object* v___x_4770_; 
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 4, v___x_4768_);
v___x_4770_ = v___x_4759_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_env_4749_);
lean_ctor_set(v_reuseFailAlloc_4773_, 1, v_nextMacroScope_4750_);
lean_ctor_set(v_reuseFailAlloc_4773_, 2, v_ngen_4751_);
lean_ctor_set(v_reuseFailAlloc_4773_, 3, v_auxDeclNGen_4752_);
lean_ctor_set(v_reuseFailAlloc_4773_, 4, v___x_4768_);
lean_ctor_set(v_reuseFailAlloc_4773_, 5, v_cache_4753_);
lean_ctor_set(v_reuseFailAlloc_4773_, 6, v_recordedDeps_4754_);
lean_ctor_set(v_reuseFailAlloc_4773_, 7, v_messages_4755_);
lean_ctor_set(v_reuseFailAlloc_4773_, 8, v_infoState_4756_);
lean_ctor_set(v_reuseFailAlloc_4773_, 9, v_snapshotTasks_4757_);
v___x_4770_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4771_ = lean_st_ref_put(v___y_4715_, v___x_4770_);
v___x_4772_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg(v_fst_4717_);
return v___x_4772_;
}
}
}
}
}
else
{
goto v___jp_4740_;
}
}
else
{
goto v___jp_4740_;
}
}
v___jp_4777_:
{
double v___x_4779_; double v___x_4780_; double v___x_4781_; uint8_t v___x_4782_; 
v___x_4779_ = lean_unbox_float(v_snd_4726_);
v___x_4780_ = lean_unbox_float(v_fst_4725_);
v___x_4781_ = lean_float_sub(v___x_4779_, v___x_4780_);
v___x_4782_ = lean_float_decLt(v___y_4778_, v___x_4781_);
v___y_4746_ = v___x_4782_;
goto v___jp_4745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___boxed(lean_object* v_cls_4793_, lean_object* v_collapsed_4794_, lean_object* v_tag_4795_, lean_object* v_opts_4796_, lean_object* v_clsEnabled_4797_, lean_object* v_oldTraces_4798_, lean_object* v_msg_4799_, lean_object* v_resStartStop_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_){
_start:
{
uint8_t v_collapsed_boxed_4806_; uint8_t v_clsEnabled_boxed_4807_; lean_object* v_res_4808_; 
v_collapsed_boxed_4806_ = lean_unbox(v_collapsed_4794_);
v_clsEnabled_boxed_4807_ = lean_unbox(v_clsEnabled_4797_);
v_res_4808_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16(v_cls_4793_, v_collapsed_boxed_4806_, v_tag_4795_, v_opts_4796_, v_clsEnabled_boxed_4807_, v_oldTraces_4798_, v_msg_4799_, v_resStartStop_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
lean_dec(v___y_4804_);
lean_dec_ref(v___y_4803_);
lean_dec(v___y_4802_);
lean_dec_ref(v___y_4801_);
lean_dec_ref(v_opts_4796_);
return v_res_4808_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__1(void){
_start:
{
lean_object* v___x_4810_; double v___x_4811_; 
v___x_4810_ = lean_unsigned_to_nat(1000000000u);
v___x_4811_ = lean_float_of_nat(v___x_4810_);
return v___x_4811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem(lean_object* v_problem_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_){
_start:
{
lean_object* v_sortInfo_4818_; lean_object* v_predInfo_4819_; lean_object* v_groundFacts_4820_; lean_object* v_quantifiedFacts_4821_; size_t v___y_4823_; lean_object* v___y_4824_; lean_object* v___y_4825_; lean_object* v___y_4841_; size_t v___y_4842_; lean_object* v___y_4843_; lean_object* v___y_4844_; lean_object* v___y_4845_; lean_object* v___y_4846_; lean_object* v___y_4849_; size_t v___y_4850_; lean_object* v___y_4851_; lean_object* v___y_4852_; lean_object* v___y_4853_; lean_object* v___y_4854_; lean_object* v___y_4857_; size_t v___y_4858_; lean_object* v___y_4859_; lean_object* v___y_4860_; lean_object* v___y_4861_; size_t v___y_4867_; lean_object* v___y_4868_; lean_object* v___y_4869_; size_t v___y_4885_; lean_object* v___y_4886_; lean_object* v___y_4887_; lean_object* v___y_4888_; lean_object* v___y_4889_; lean_object* v___y_4890_; size_t v___y_4893_; lean_object* v___y_4894_; lean_object* v___y_4895_; lean_object* v___y_4896_; lean_object* v___y_4897_; lean_object* v___y_4898_; lean_object* v___y_4901_; size_t v___y_4902_; lean_object* v___y_4903_; lean_object* v___y_4904_; lean_object* v___y_4905_; lean_object* v_size_4910_; lean_object* v_buckets_4911_; lean_object* v___f_4912_; lean_object* v_cls_4913_; uint8_t v___y_4915_; uint8_t v___y_4916_; lean_object* v___y_4917_; lean_object* v___y_4918_; lean_object* v___y_4919_; lean_object* v___y_4920_; lean_object* v_a_4921_; uint8_t v___y_4931_; uint8_t v___y_4932_; lean_object* v___y_4933_; lean_object* v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; lean_object* v_a_4937_; uint8_t v___y_4940_; uint8_t v___y_4941_; lean_object* v___y_4942_; size_t v___y_4943_; lean_object* v___y_4944_; lean_object* v___y_4945_; lean_object* v___y_4946_; lean_object* v___y_4947_; lean_object* v___y_4948_; uint8_t v___y_4967_; uint8_t v___y_4968_; size_t v___y_4969_; lean_object* v___y_4970_; lean_object* v___y_4971_; lean_object* v___y_4972_; lean_object* v___y_4973_; lean_object* v___y_4974_; lean_object* v___y_4975_; lean_object* v___y_4976_; lean_object* v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_4981_; uint8_t v___y_4982_; uint8_t v___y_4983_; lean_object* v___y_4984_; lean_object* v___y_4985_; size_t v___y_4986_; lean_object* v___y_4987_; lean_object* v___y_4988_; lean_object* v___y_4989_; lean_object* v___y_4990_; lean_object* v___y_4991_; lean_object* v___y_4992_; lean_object* v___y_4995_; uint8_t v___y_4996_; uint8_t v___y_4997_; size_t v___y_4998_; lean_object* v___y_4999_; lean_object* v___y_5000_; lean_object* v___y_5001_; lean_object* v___y_5002_; lean_object* v___y_5003_; lean_object* v___y_5004_; lean_object* v___y_5005_; uint8_t v___y_5011_; uint8_t v___y_5012_; lean_object* v___y_5013_; lean_object* v___y_5014_; lean_object* v___y_5015_; lean_object* v___y_5016_; lean_object* v_a_5017_; uint8_t v___y_5030_; uint8_t v___y_5031_; lean_object* v___y_5032_; lean_object* v___y_5033_; lean_object* v___y_5034_; lean_object* v___y_5035_; lean_object* v_a_5036_; uint8_t v___y_5039_; uint8_t v___y_5040_; lean_object* v___y_5041_; size_t v___y_5042_; lean_object* v___y_5043_; lean_object* v___y_5044_; lean_object* v___y_5045_; lean_object* v___y_5046_; lean_object* v___y_5047_; lean_object* v___y_5066_; uint8_t v___y_5067_; uint8_t v___y_5068_; size_t v___y_5069_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___y_5072_; lean_object* v___y_5073_; lean_object* v___y_5074_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v___y_5077_; lean_object* v___y_5080_; uint8_t v___y_5081_; lean_object* v___y_5082_; uint8_t v___y_5083_; lean_object* v___y_5084_; size_t v___y_5085_; lean_object* v___y_5086_; lean_object* v___y_5087_; lean_object* v___y_5088_; lean_object* v___y_5089_; lean_object* v___y_5090_; lean_object* v___y_5091_; lean_object* v___y_5094_; uint8_t v___y_5095_; uint8_t v___y_5096_; size_t v___y_5097_; lean_object* v___y_5098_; lean_object* v___y_5099_; lean_object* v___y_5100_; lean_object* v___y_5101_; lean_object* v___y_5102_; lean_object* v___y_5103_; lean_object* v___y_5104_; lean_object* v___y_5110_; size_t v___y_5111_; uint8_t v___y_5112_; uint8_t v___y_5113_; size_t v___y_5114_; lean_object* v___y_5115_; lean_object* v___y_5116_; lean_object* v___y_5117_; lean_object* v___y_5118_; lean_object* v___y_5119_; lean_object* v___y_5145_; lean_object* v___y_5146_; lean_object* v___y_5147_; lean_object* v___y_5177_; lean_object* v___y_5178_; lean_object* v___y_5179_; lean_object* v___y_5180_; lean_object* v___y_5181_; lean_object* v___y_5182_; lean_object* v___y_5185_; lean_object* v___y_5186_; lean_object* v___y_5187_; lean_object* v___y_5188_; lean_object* v___y_5189_; lean_object* v___y_5190_; lean_object* v___y_5193_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; uint8_t v___x_5203_; 
v_sortInfo_4818_ = lean_ctor_get(v_problem_4812_, 0);
v_predInfo_4819_ = lean_ctor_get(v_problem_4812_, 2);
v_groundFacts_4820_ = lean_ctor_get(v_problem_4812_, 3);
v_quantifiedFacts_4821_ = lean_ctor_get(v_problem_4812_, 4);
v_size_4910_ = lean_ctor_get(v_sortInfo_4818_, 0);
v_buckets_4911_ = lean_ctor_get(v_sortInfo_4818_, 1);
v___f_4912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__0));
v_cls_4913_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_5200_ = lean_mk_empty_array_with_capacity(v_size_4910_);
v___x_5201_ = lean_unsigned_to_nat(0u);
v___x_5202_ = lean_array_get_size(v_buckets_4911_);
v___x_5203_ = lean_nat_dec_lt(v___x_5201_, v___x_5202_);
if (v___x_5203_ == 0)
{
v___y_5193_ = v___x_5200_;
goto v___jp_5192_;
}
else
{
size_t v___x_5204_; size_t v___x_5205_; lean_object* v___x_5206_; 
v___x_5204_ = ((size_t)0ULL);
v___x_5205_ = lean_usize_of_nat(v___x_5202_);
v___x_5206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__19(v_buckets_4911_, v___x_5204_, v___x_5205_, v___x_5200_);
v___y_5193_ = v___x_5206_;
goto v___jp_5192_;
}
v___jp_4822_:
{
size_t v_sz_4826_; lean_object* v___x_4827_; 
v_sz_4826_ = lean_array_size(v___y_4825_);
v___x_4827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8(v_sortInfo_4818_, v___y_4825_, v_sz_4826_, v___y_4823_, v___y_4824_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
lean_dec_ref(v___y_4825_);
if (lean_obj_tag(v___x_4827_) == 0)
{
size_t v_sz_4828_; lean_object* v___x_4829_; 
lean_dec_ref_known(v___x_4827_, 1);
v_sz_4828_ = lean_array_size(v_groundFacts_4820_);
v___x_4829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9(v_groundFacts_4820_, v_sz_4828_, v___y_4823_, v___y_4824_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
if (lean_obj_tag(v___x_4829_) == 0)
{
size_t v_sz_4830_; lean_object* v___x_4831_; 
lean_dec_ref_known(v___x_4829_, 1);
v_sz_4830_ = lean_array_size(v_quantifiedFacts_4821_);
v___x_4831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10(v_quantifiedFacts_4821_, v_sz_4830_, v___y_4823_, v___y_4824_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4838_; 
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4838_ == 0)
{
lean_object* v_unused_4839_; 
v_unused_4839_ = lean_ctor_get(v___x_4831_, 0);
lean_dec(v_unused_4839_);
v___x_4833_ = v___x_4831_;
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
else
{
lean_dec(v___x_4831_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4836_; 
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 0, v___y_4824_);
v___x_4836_ = v___x_4833_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v___y_4824_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
else
{
return v___x_4831_;
}
}
else
{
return v___x_4829_;
}
}
else
{
return v___x_4827_;
}
}
v___jp_4840_:
{
lean_object* v___x_4847_; 
v___x_4847_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v___y_4844_, v___y_4841_, v___y_4845_, v___y_4846_);
lean_dec(v___y_4846_);
lean_dec(v___y_4844_);
v___y_4823_ = v___y_4842_;
v___y_4824_ = v___y_4843_;
v___y_4825_ = v___x_4847_;
goto v___jp_4822_;
}
v___jp_4848_:
{
uint8_t v___x_4855_; 
v___x_4855_ = lean_nat_dec_le(v___y_4854_, v___y_4852_);
if (v___x_4855_ == 0)
{
lean_dec(v___y_4852_);
lean_inc(v___y_4854_);
v___y_4841_ = v___y_4849_;
v___y_4842_ = v___y_4850_;
v___y_4843_ = v___y_4851_;
v___y_4844_ = v___y_4853_;
v___y_4845_ = v___y_4854_;
v___y_4846_ = v___y_4854_;
goto v___jp_4840_;
}
else
{
v___y_4841_ = v___y_4849_;
v___y_4842_ = v___y_4850_;
v___y_4843_ = v___y_4851_;
v___y_4844_ = v___y_4853_;
v___y_4845_ = v___y_4854_;
v___y_4846_ = v___y_4852_;
goto v___jp_4840_;
}
}
v___jp_4856_:
{
lean_object* v___x_4862_; uint8_t v___x_4863_; 
v___x_4862_ = lean_array_get_size(v___y_4861_);
v___x_4863_ = lean_nat_dec_eq(v___x_4862_, v___y_4857_);
if (v___x_4863_ == 0)
{
lean_object* v___x_4864_; uint8_t v___x_4865_; 
v___x_4864_ = lean_nat_sub(v___x_4862_, v___y_4860_);
v___x_4865_ = lean_nat_dec_le(v___y_4857_, v___x_4864_);
if (v___x_4865_ == 0)
{
lean_dec(v___y_4857_);
lean_inc(v___x_4864_);
v___y_4849_ = v___y_4861_;
v___y_4850_ = v___y_4858_;
v___y_4851_ = v___y_4859_;
v___y_4852_ = v___x_4864_;
v___y_4853_ = v___x_4862_;
v___y_4854_ = v___x_4864_;
goto v___jp_4848_;
}
else
{
v___y_4849_ = v___y_4861_;
v___y_4850_ = v___y_4858_;
v___y_4851_ = v___y_4859_;
v___y_4852_ = v___x_4864_;
v___y_4853_ = v___x_4862_;
v___y_4854_ = v___y_4857_;
goto v___jp_4848_;
}
}
else
{
lean_dec(v___y_4857_);
v___y_4823_ = v___y_4858_;
v___y_4824_ = v___y_4859_;
v___y_4825_ = v___y_4861_;
goto v___jp_4822_;
}
}
v___jp_4866_:
{
size_t v_sz_4870_; lean_object* v___x_4871_; 
v_sz_4870_ = lean_array_size(v___y_4869_);
v___x_4871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8(v_sortInfo_4818_, v___y_4869_, v_sz_4870_, v___y_4867_, v___y_4868_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
lean_dec_ref(v___y_4869_);
if (lean_obj_tag(v___x_4871_) == 0)
{
size_t v_sz_4872_; lean_object* v___x_4873_; 
lean_dec_ref_known(v___x_4871_, 1);
v_sz_4872_ = lean_array_size(v_groundFacts_4820_);
v___x_4873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9(v_groundFacts_4820_, v_sz_4872_, v___y_4867_, v___y_4868_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
if (lean_obj_tag(v___x_4873_) == 0)
{
size_t v_sz_4874_; lean_object* v___x_4875_; 
lean_dec_ref_known(v___x_4873_, 1);
v_sz_4874_ = lean_array_size(v_quantifiedFacts_4821_);
v___x_4875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10(v_quantifiedFacts_4821_, v_sz_4874_, v___y_4867_, v___y_4868_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4882_; 
v_isSharedCheck_4882_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4882_ == 0)
{
lean_object* v_unused_4883_; 
v_unused_4883_ = lean_ctor_get(v___x_4875_, 0);
lean_dec(v_unused_4883_);
v___x_4877_ = v___x_4875_;
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
else
{
lean_dec(v___x_4875_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
lean_object* v___x_4880_; 
if (v_isShared_4878_ == 0)
{
lean_ctor_set(v___x_4877_, 0, v___y_4868_);
v___x_4880_ = v___x_4877_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v___y_4868_);
v___x_4880_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
return v___x_4880_;
}
}
}
else
{
return v___x_4875_;
}
}
else
{
return v___x_4873_;
}
}
else
{
return v___x_4871_;
}
}
v___jp_4884_:
{
lean_object* v___x_4891_; 
v___x_4891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v___y_4888_, v___y_4889_, v___y_4887_, v___y_4890_);
lean_dec(v___y_4890_);
lean_dec(v___y_4888_);
v___y_4867_ = v___y_4885_;
v___y_4868_ = v___y_4886_;
v___y_4869_ = v___x_4891_;
goto v___jp_4866_;
}
v___jp_4892_:
{
uint8_t v___x_4899_; 
v___x_4899_ = lean_nat_dec_le(v___y_4898_, v___y_4897_);
if (v___x_4899_ == 0)
{
lean_dec(v___y_4897_);
lean_inc(v___y_4898_);
v___y_4885_ = v___y_4893_;
v___y_4886_ = v___y_4894_;
v___y_4887_ = v___y_4898_;
v___y_4888_ = v___y_4895_;
v___y_4889_ = v___y_4896_;
v___y_4890_ = v___y_4898_;
goto v___jp_4884_;
}
else
{
v___y_4885_ = v___y_4893_;
v___y_4886_ = v___y_4894_;
v___y_4887_ = v___y_4898_;
v___y_4888_ = v___y_4895_;
v___y_4889_ = v___y_4896_;
v___y_4890_ = v___y_4897_;
goto v___jp_4884_;
}
}
v___jp_4900_:
{
lean_object* v___x_4906_; uint8_t v___x_4907_; 
v___x_4906_ = lean_array_get_size(v___y_4905_);
v___x_4907_ = lean_nat_dec_eq(v___x_4906_, v___y_4901_);
if (v___x_4907_ == 0)
{
lean_object* v___x_4908_; uint8_t v___x_4909_; 
v___x_4908_ = lean_nat_sub(v___x_4906_, v___y_4904_);
v___x_4909_ = lean_nat_dec_le(v___y_4901_, v___x_4908_);
if (v___x_4909_ == 0)
{
lean_dec(v___y_4901_);
lean_inc(v___x_4908_);
v___y_4893_ = v___y_4902_;
v___y_4894_ = v___y_4903_;
v___y_4895_ = v___x_4906_;
v___y_4896_ = v___y_4905_;
v___y_4897_ = v___x_4908_;
v___y_4898_ = v___x_4908_;
goto v___jp_4892_;
}
else
{
v___y_4893_ = v___y_4902_;
v___y_4894_ = v___y_4903_;
v___y_4895_ = v___x_4906_;
v___y_4896_ = v___y_4905_;
v___y_4897_ = v___x_4908_;
v___y_4898_ = v___y_4901_;
goto v___jp_4892_;
}
}
else
{
lean_dec(v___y_4901_);
v___y_4867_ = v___y_4902_;
v___y_4868_ = v___y_4903_;
v___y_4869_ = v___y_4905_;
goto v___jp_4866_;
}
}
v___jp_4914_:
{
lean_object* v___x_4922_; double v___x_4923_; double v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4922_ = lean_io_get_num_heartbeats();
v___x_4923_ = lean_float_of_nat(v___y_4920_);
v___x_4924_ = lean_float_of_nat(v___x_4922_);
v___x_4925_ = lean_box_float(v___x_4923_);
v___x_4926_ = lean_box_float(v___x_4924_);
v___x_4927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4925_);
lean_ctor_set(v___x_4927_, 1, v___x_4926_);
v___x_4928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4928_, 0, v_a_4921_);
lean_ctor_set(v___x_4928_, 1, v___x_4927_);
lean_inc_ref(v___y_4919_);
v___x_4929_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16(v_cls_4913_, v___y_4915_, v___y_4919_, v___y_4917_, v___y_4916_, v___y_4918_, v___f_4912_, v___x_4928_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
return v___x_4929_;
}
v___jp_4930_:
{
lean_object* v___x_4938_; 
v___x_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4938_, 0, v_a_4937_);
v___y_4915_ = v___y_4931_;
v___y_4916_ = v___y_4932_;
v___y_4917_ = v___y_4933_;
v___y_4918_ = v___y_4934_;
v___y_4919_ = v___y_4935_;
v___y_4920_ = v___y_4936_;
v_a_4921_ = v___x_4938_;
goto v___jp_4914_;
}
v___jp_4939_:
{
size_t v_sz_4949_; lean_object* v___x_4950_; 
v_sz_4949_ = lean_array_size(v___y_4948_);
v___x_4950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8(v_sortInfo_4818_, v___y_4948_, v_sz_4949_, v___y_4943_, v___y_4944_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
lean_dec_ref(v___y_4948_);
if (lean_obj_tag(v___x_4950_) == 0)
{
size_t v_sz_4951_; lean_object* v___x_4952_; 
lean_dec_ref_known(v___x_4950_, 1);
v_sz_4951_ = lean_array_size(v_groundFacts_4820_);
v___x_4952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9(v_groundFacts_4820_, v_sz_4951_, v___y_4943_, v___y_4944_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
if (lean_obj_tag(v___x_4952_) == 0)
{
size_t v_sz_4953_; lean_object* v___x_4954_; 
lean_dec_ref_known(v___x_4952_, 1);
v_sz_4953_ = lean_array_size(v_quantifiedFacts_4821_);
v___x_4954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10(v_quantifiedFacts_4821_, v_sz_4953_, v___y_4943_, v___y_4944_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4961_; 
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4961_ == 0)
{
lean_object* v_unused_4962_; 
v_unused_4962_ = lean_ctor_get(v___x_4954_, 0);
lean_dec(v_unused_4962_);
v___x_4956_ = v___x_4954_;
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
else
{
lean_dec(v___x_4954_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4959_; 
if (v_isShared_4957_ == 0)
{
lean_ctor_set_tag(v___x_4956_, 1);
lean_ctor_set(v___x_4956_, 0, v___y_4944_);
v___x_4959_ = v___x_4956_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___y_4944_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
v___y_4915_ = v___y_4940_;
v___y_4916_ = v___y_4941_;
v___y_4917_ = v___y_4942_;
v___y_4918_ = v___y_4945_;
v___y_4919_ = v___y_4946_;
v___y_4920_ = v___y_4947_;
v_a_4921_ = v___x_4959_;
goto v___jp_4914_;
}
}
}
else
{
lean_object* v_a_4963_; 
v_a_4963_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_a_4963_);
lean_dec_ref_known(v___x_4954_, 1);
v___y_4931_ = v___y_4940_;
v___y_4932_ = v___y_4941_;
v___y_4933_ = v___y_4942_;
v___y_4934_ = v___y_4945_;
v___y_4935_ = v___y_4946_;
v___y_4936_ = v___y_4947_;
v_a_4937_ = v_a_4963_;
goto v___jp_4930_;
}
}
else
{
lean_object* v_a_4964_; 
v_a_4964_ = lean_ctor_get(v___x_4952_, 0);
lean_inc(v_a_4964_);
lean_dec_ref_known(v___x_4952_, 1);
v___y_4931_ = v___y_4940_;
v___y_4932_ = v___y_4941_;
v___y_4933_ = v___y_4942_;
v___y_4934_ = v___y_4945_;
v___y_4935_ = v___y_4946_;
v___y_4936_ = v___y_4947_;
v_a_4937_ = v_a_4964_;
goto v___jp_4930_;
}
}
else
{
lean_object* v_a_4965_; 
v_a_4965_ = lean_ctor_get(v___x_4950_, 0);
lean_inc(v_a_4965_);
lean_dec_ref_known(v___x_4950_, 1);
v___y_4931_ = v___y_4940_;
v___y_4932_ = v___y_4941_;
v___y_4933_ = v___y_4942_;
v___y_4934_ = v___y_4945_;
v___y_4935_ = v___y_4946_;
v___y_4936_ = v___y_4947_;
v_a_4937_ = v_a_4965_;
goto v___jp_4930_;
}
}
v___jp_4966_:
{
lean_object* v___x_4979_; 
v___x_4979_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v___y_4971_, v___y_4973_, v___y_4976_, v___y_4978_);
lean_dec(v___y_4978_);
lean_dec(v___y_4971_);
v___y_4940_ = v___y_4967_;
v___y_4941_ = v___y_4968_;
v___y_4942_ = v___y_4970_;
v___y_4943_ = v___y_4969_;
v___y_4944_ = v___y_4972_;
v___y_4945_ = v___y_4974_;
v___y_4946_ = v___y_4975_;
v___y_4947_ = v___y_4977_;
v___y_4948_ = v___x_4979_;
goto v___jp_4939_;
}
v___jp_4980_:
{
uint8_t v___x_4993_; 
v___x_4993_ = lean_nat_dec_le(v___y_4992_, v___y_4981_);
if (v___x_4993_ == 0)
{
lean_dec(v___y_4981_);
lean_inc(v___y_4992_);
v___y_4967_ = v___y_4982_;
v___y_4968_ = v___y_4983_;
v___y_4969_ = v___y_4986_;
v___y_4970_ = v___y_4985_;
v___y_4971_ = v___y_4984_;
v___y_4972_ = v___y_4988_;
v___y_4973_ = v___y_4987_;
v___y_4974_ = v___y_4989_;
v___y_4975_ = v___y_4990_;
v___y_4976_ = v___y_4992_;
v___y_4977_ = v___y_4991_;
v___y_4978_ = v___y_4992_;
goto v___jp_4966_;
}
else
{
v___y_4967_ = v___y_4982_;
v___y_4968_ = v___y_4983_;
v___y_4969_ = v___y_4986_;
v___y_4970_ = v___y_4985_;
v___y_4971_ = v___y_4984_;
v___y_4972_ = v___y_4988_;
v___y_4973_ = v___y_4987_;
v___y_4974_ = v___y_4989_;
v___y_4975_ = v___y_4990_;
v___y_4976_ = v___y_4992_;
v___y_4977_ = v___y_4991_;
v___y_4978_ = v___y_4981_;
goto v___jp_4966_;
}
}
v___jp_4994_:
{
lean_object* v___x_5006_; uint8_t v___x_5007_; 
v___x_5006_ = lean_array_get_size(v___y_5005_);
v___x_5007_ = lean_nat_dec_eq(v___x_5006_, v___y_4995_);
if (v___x_5007_ == 0)
{
lean_object* v___x_5008_; uint8_t v___x_5009_; 
v___x_5008_ = lean_nat_sub(v___x_5006_, v___y_5001_);
v___x_5009_ = lean_nat_dec_le(v___y_4995_, v___x_5008_);
if (v___x_5009_ == 0)
{
lean_dec(v___y_4995_);
lean_inc(v___x_5008_);
v___y_4981_ = v___x_5008_;
v___y_4982_ = v___y_4996_;
v___y_4983_ = v___y_4997_;
v___y_4984_ = v___x_5006_;
v___y_4985_ = v___y_4999_;
v___y_4986_ = v___y_4998_;
v___y_4987_ = v___y_5005_;
v___y_4988_ = v___y_5000_;
v___y_4989_ = v___y_5002_;
v___y_4990_ = v___y_5003_;
v___y_4991_ = v___y_5004_;
v___y_4992_ = v___x_5008_;
goto v___jp_4980_;
}
else
{
v___y_4981_ = v___x_5008_;
v___y_4982_ = v___y_4996_;
v___y_4983_ = v___y_4997_;
v___y_4984_ = v___x_5006_;
v___y_4985_ = v___y_4999_;
v___y_4986_ = v___y_4998_;
v___y_4987_ = v___y_5005_;
v___y_4988_ = v___y_5000_;
v___y_4989_ = v___y_5002_;
v___y_4990_ = v___y_5003_;
v___y_4991_ = v___y_5004_;
v___y_4992_ = v___y_4995_;
goto v___jp_4980_;
}
}
else
{
lean_dec(v___y_4995_);
v___y_4940_ = v___y_4996_;
v___y_4941_ = v___y_4997_;
v___y_4942_ = v___y_4999_;
v___y_4943_ = v___y_4998_;
v___y_4944_ = v___y_5000_;
v___y_4945_ = v___y_5002_;
v___y_4946_ = v___y_5003_;
v___y_4947_ = v___y_5004_;
v___y_4948_ = v___y_5005_;
goto v___jp_4939_;
}
}
v___jp_5010_:
{
lean_object* v___x_5018_; double v___x_5019_; double v___x_5020_; double v___x_5021_; double v___x_5022_; double v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; 
v___x_5018_ = lean_io_mono_nanos_now();
v___x_5019_ = lean_float_of_nat(v___y_5014_);
v___x_5020_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__1);
v___x_5021_ = lean_float_div(v___x_5019_, v___x_5020_);
v___x_5022_ = lean_float_of_nat(v___x_5018_);
v___x_5023_ = lean_float_div(v___x_5022_, v___x_5020_);
v___x_5024_ = lean_box_float(v___x_5021_);
v___x_5025_ = lean_box_float(v___x_5023_);
v___x_5026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5024_);
lean_ctor_set(v___x_5026_, 1, v___x_5025_);
v___x_5027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5027_, 0, v_a_5017_);
lean_ctor_set(v___x_5027_, 1, v___x_5026_);
lean_inc_ref(v___y_5016_);
v___x_5028_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16(v_cls_4913_, v___y_5011_, v___y_5016_, v___y_5013_, v___y_5012_, v___y_5015_, v___f_4912_, v___x_5027_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
return v___x_5028_;
}
v___jp_5029_:
{
lean_object* v___x_5037_; 
v___x_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5037_, 0, v_a_5036_);
v___y_5011_ = v___y_5030_;
v___y_5012_ = v___y_5031_;
v___y_5013_ = v___y_5032_;
v___y_5014_ = v___y_5033_;
v___y_5015_ = v___y_5034_;
v___y_5016_ = v___y_5035_;
v_a_5017_ = v___x_5037_;
goto v___jp_5010_;
}
v___jp_5038_:
{
size_t v_sz_5048_; lean_object* v___x_5049_; 
v_sz_5048_ = lean_array_size(v___y_5047_);
v___x_5049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8(v_sortInfo_4818_, v___y_5047_, v_sz_5048_, v___y_5042_, v___y_5043_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
lean_dec_ref(v___y_5047_);
if (lean_obj_tag(v___x_5049_) == 0)
{
size_t v_sz_5050_; lean_object* v___x_5051_; 
lean_dec_ref_known(v___x_5049_, 1);
v_sz_5050_ = lean_array_size(v_groundFacts_4820_);
v___x_5051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9(v_groundFacts_4820_, v_sz_5050_, v___y_5042_, v___y_5043_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
if (lean_obj_tag(v___x_5051_) == 0)
{
size_t v_sz_5052_; lean_object* v___x_5053_; 
lean_dec_ref_known(v___x_5051_, 1);
v_sz_5052_ = lean_array_size(v_quantifiedFacts_4821_);
v___x_5053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10(v_quantifiedFacts_4821_, v_sz_5052_, v___y_5042_, v___y_5043_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
if (lean_obj_tag(v___x_5053_) == 0)
{
lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5060_; 
v_isSharedCheck_5060_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5060_ == 0)
{
lean_object* v_unused_5061_; 
v_unused_5061_ = lean_ctor_get(v___x_5053_, 0);
lean_dec(v_unused_5061_);
v___x_5055_ = v___x_5053_;
v_isShared_5056_ = v_isSharedCheck_5060_;
goto v_resetjp_5054_;
}
else
{
lean_dec(v___x_5053_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5060_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
lean_object* v___x_5058_; 
if (v_isShared_5056_ == 0)
{
lean_ctor_set_tag(v___x_5055_, 1);
lean_ctor_set(v___x_5055_, 0, v___y_5043_);
v___x_5058_ = v___x_5055_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v___y_5043_);
v___x_5058_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
v___y_5011_ = v___y_5039_;
v___y_5012_ = v___y_5040_;
v___y_5013_ = v___y_5041_;
v___y_5014_ = v___y_5044_;
v___y_5015_ = v___y_5045_;
v___y_5016_ = v___y_5046_;
v_a_5017_ = v___x_5058_;
goto v___jp_5010_;
}
}
}
else
{
lean_object* v_a_5062_; 
v_a_5062_ = lean_ctor_get(v___x_5053_, 0);
lean_inc(v_a_5062_);
lean_dec_ref_known(v___x_5053_, 1);
v___y_5030_ = v___y_5039_;
v___y_5031_ = v___y_5040_;
v___y_5032_ = v___y_5041_;
v___y_5033_ = v___y_5044_;
v___y_5034_ = v___y_5045_;
v___y_5035_ = v___y_5046_;
v_a_5036_ = v_a_5062_;
goto v___jp_5029_;
}
}
else
{
lean_object* v_a_5063_; 
v_a_5063_ = lean_ctor_get(v___x_5051_, 0);
lean_inc(v_a_5063_);
lean_dec_ref_known(v___x_5051_, 1);
v___y_5030_ = v___y_5039_;
v___y_5031_ = v___y_5040_;
v___y_5032_ = v___y_5041_;
v___y_5033_ = v___y_5044_;
v___y_5034_ = v___y_5045_;
v___y_5035_ = v___y_5046_;
v_a_5036_ = v_a_5063_;
goto v___jp_5029_;
}
}
else
{
lean_object* v_a_5064_; 
v_a_5064_ = lean_ctor_get(v___x_5049_, 0);
lean_inc(v_a_5064_);
lean_dec_ref_known(v___x_5049_, 1);
v___y_5030_ = v___y_5039_;
v___y_5031_ = v___y_5040_;
v___y_5032_ = v___y_5041_;
v___y_5033_ = v___y_5044_;
v___y_5034_ = v___y_5045_;
v___y_5035_ = v___y_5046_;
v_a_5036_ = v_a_5064_;
goto v___jp_5029_;
}
}
v___jp_5065_:
{
lean_object* v___x_5078_; 
v___x_5078_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v___y_5075_, v___y_5066_, v___y_5076_, v___y_5077_);
lean_dec(v___y_5077_);
lean_dec(v___y_5075_);
v___y_5039_ = v___y_5067_;
v___y_5040_ = v___y_5068_;
v___y_5041_ = v___y_5070_;
v___y_5042_ = v___y_5069_;
v___y_5043_ = v___y_5071_;
v___y_5044_ = v___y_5072_;
v___y_5045_ = v___y_5073_;
v___y_5046_ = v___y_5074_;
v___y_5047_ = v___x_5078_;
goto v___jp_5038_;
}
v___jp_5079_:
{
uint8_t v___x_5092_; 
v___x_5092_ = lean_nat_dec_le(v___y_5091_, v___y_5082_);
if (v___x_5092_ == 0)
{
lean_dec(v___y_5082_);
lean_inc(v___y_5091_);
v___y_5066_ = v___y_5080_;
v___y_5067_ = v___y_5081_;
v___y_5068_ = v___y_5083_;
v___y_5069_ = v___y_5085_;
v___y_5070_ = v___y_5084_;
v___y_5071_ = v___y_5086_;
v___y_5072_ = v___y_5087_;
v___y_5073_ = v___y_5088_;
v___y_5074_ = v___y_5090_;
v___y_5075_ = v___y_5089_;
v___y_5076_ = v___y_5091_;
v___y_5077_ = v___y_5091_;
goto v___jp_5065_;
}
else
{
v___y_5066_ = v___y_5080_;
v___y_5067_ = v___y_5081_;
v___y_5068_ = v___y_5083_;
v___y_5069_ = v___y_5085_;
v___y_5070_ = v___y_5084_;
v___y_5071_ = v___y_5086_;
v___y_5072_ = v___y_5087_;
v___y_5073_ = v___y_5088_;
v___y_5074_ = v___y_5090_;
v___y_5075_ = v___y_5089_;
v___y_5076_ = v___y_5091_;
v___y_5077_ = v___y_5082_;
goto v___jp_5065_;
}
}
v___jp_5093_:
{
lean_object* v___x_5105_; uint8_t v___x_5106_; 
v___x_5105_ = lean_array_get_size(v___y_5104_);
v___x_5106_ = lean_nat_dec_eq(v___x_5105_, v___y_5094_);
if (v___x_5106_ == 0)
{
lean_object* v___x_5107_; uint8_t v___x_5108_; 
v___x_5107_ = lean_nat_sub(v___x_5105_, v___y_5100_);
v___x_5108_ = lean_nat_dec_le(v___y_5094_, v___x_5107_);
if (v___x_5108_ == 0)
{
lean_dec(v___y_5094_);
lean_inc(v___x_5107_);
v___y_5080_ = v___y_5104_;
v___y_5081_ = v___y_5095_;
v___y_5082_ = v___x_5107_;
v___y_5083_ = v___y_5096_;
v___y_5084_ = v___y_5098_;
v___y_5085_ = v___y_5097_;
v___y_5086_ = v___y_5099_;
v___y_5087_ = v___y_5101_;
v___y_5088_ = v___y_5102_;
v___y_5089_ = v___x_5105_;
v___y_5090_ = v___y_5103_;
v___y_5091_ = v___x_5107_;
goto v___jp_5079_;
}
else
{
v___y_5080_ = v___y_5104_;
v___y_5081_ = v___y_5095_;
v___y_5082_ = v___x_5107_;
v___y_5083_ = v___y_5096_;
v___y_5084_ = v___y_5098_;
v___y_5085_ = v___y_5097_;
v___y_5086_ = v___y_5099_;
v___y_5087_ = v___y_5101_;
v___y_5088_ = v___y_5102_;
v___y_5089_ = v___x_5105_;
v___y_5090_ = v___y_5103_;
v___y_5091_ = v___y_5094_;
goto v___jp_5079_;
}
}
else
{
lean_dec(v___y_5094_);
v___y_5039_ = v___y_5095_;
v___y_5040_ = v___y_5096_;
v___y_5041_ = v___y_5098_;
v___y_5042_ = v___y_5097_;
v___y_5043_ = v___y_5099_;
v___y_5044_ = v___y_5101_;
v___y_5045_ = v___y_5102_;
v___y_5046_ = v___y_5103_;
v___y_5047_ = v___y_5104_;
goto v___jp_5038_;
}
}
v___jp_5109_:
{
lean_object* v___x_5120_; lean_object* v_a_5121_; lean_object* v___x_5122_; uint8_t v___x_5123_; 
v___x_5120_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg(v_a_4816_);
v_a_5121_ = lean_ctor_get(v___x_5120_, 0);
lean_inc(v_a_5121_);
lean_dec_ref(v___x_5120_);
v___x_5122_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5123_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15(v___y_5115_, v___x_5122_);
if (v___x_5123_ == 0)
{
lean_object* v___x_5124_; lean_object* v___x_5125_; 
v___x_5124_ = lean_io_mono_nanos_now();
v___x_5125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7(v___y_5119_, v___y_5111_, v___y_5114_, v___y_5117_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
lean_dec_ref(v___y_5119_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_size_5126_; lean_object* v_buckets_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; uint8_t v___x_5130_; 
lean_dec_ref_known(v___x_5125_, 1);
v_size_5126_ = lean_ctor_get(v_predInfo_4819_, 0);
v_buckets_5127_ = lean_ctor_get(v_predInfo_4819_, 1);
v___x_5128_ = lean_mk_empty_array_with_capacity(v_size_5126_);
v___x_5129_ = lean_array_get_size(v_buckets_5127_);
v___x_5130_ = lean_nat_dec_lt(v___y_5110_, v___x_5129_);
if (v___x_5130_ == 0)
{
v___y_5094_ = v___y_5110_;
v___y_5095_ = v___y_5112_;
v___y_5096_ = v___y_5113_;
v___y_5097_ = v___y_5114_;
v___y_5098_ = v___y_5115_;
v___y_5099_ = v___y_5117_;
v___y_5100_ = v___y_5116_;
v___y_5101_ = v___x_5124_;
v___y_5102_ = v_a_5121_;
v___y_5103_ = v___y_5118_;
v___y_5104_ = v___x_5128_;
goto v___jp_5093_;
}
else
{
size_t v___x_5131_; lean_object* v___x_5132_; 
v___x_5131_ = lean_usize_of_nat(v___x_5129_);
v___x_5132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13(v_buckets_5127_, v___y_5114_, v___x_5131_, v___x_5128_);
v___y_5094_ = v___y_5110_;
v___y_5095_ = v___y_5112_;
v___y_5096_ = v___y_5113_;
v___y_5097_ = v___y_5114_;
v___y_5098_ = v___y_5115_;
v___y_5099_ = v___y_5117_;
v___y_5100_ = v___y_5116_;
v___y_5101_ = v___x_5124_;
v___y_5102_ = v_a_5121_;
v___y_5103_ = v___y_5118_;
v___y_5104_ = v___x_5132_;
goto v___jp_5093_;
}
}
else
{
lean_object* v_a_5133_; 
lean_dec(v___y_5110_);
v_a_5133_ = lean_ctor_get(v___x_5125_, 0);
lean_inc(v_a_5133_);
lean_dec_ref_known(v___x_5125_, 1);
v___y_5030_ = v___y_5112_;
v___y_5031_ = v___y_5113_;
v___y_5032_ = v___y_5115_;
v___y_5033_ = v___x_5124_;
v___y_5034_ = v_a_5121_;
v___y_5035_ = v___y_5118_;
v_a_5036_ = v_a_5133_;
goto v___jp_5029_;
}
}
else
{
lean_object* v___x_5134_; lean_object* v___x_5135_; 
v___x_5134_ = lean_io_get_num_heartbeats();
v___x_5135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7(v___y_5119_, v___y_5111_, v___y_5114_, v___y_5117_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
lean_dec_ref(v___y_5119_);
if (lean_obj_tag(v___x_5135_) == 0)
{
lean_object* v_size_5136_; lean_object* v_buckets_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; uint8_t v___x_5140_; 
lean_dec_ref_known(v___x_5135_, 1);
v_size_5136_ = lean_ctor_get(v_predInfo_4819_, 0);
v_buckets_5137_ = lean_ctor_get(v_predInfo_4819_, 1);
v___x_5138_ = lean_mk_empty_array_with_capacity(v_size_5136_);
v___x_5139_ = lean_array_get_size(v_buckets_5137_);
v___x_5140_ = lean_nat_dec_lt(v___y_5110_, v___x_5139_);
if (v___x_5140_ == 0)
{
v___y_4995_ = v___y_5110_;
v___y_4996_ = v___y_5112_;
v___y_4997_ = v___y_5113_;
v___y_4998_ = v___y_5114_;
v___y_4999_ = v___y_5115_;
v___y_5000_ = v___y_5117_;
v___y_5001_ = v___y_5116_;
v___y_5002_ = v_a_5121_;
v___y_5003_ = v___y_5118_;
v___y_5004_ = v___x_5134_;
v___y_5005_ = v___x_5138_;
goto v___jp_4994_;
}
else
{
size_t v___x_5141_; lean_object* v___x_5142_; 
v___x_5141_ = lean_usize_of_nat(v___x_5139_);
v___x_5142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13(v_buckets_5137_, v___y_5114_, v___x_5141_, v___x_5138_);
v___y_4995_ = v___y_5110_;
v___y_4996_ = v___y_5112_;
v___y_4997_ = v___y_5113_;
v___y_4998_ = v___y_5114_;
v___y_4999_ = v___y_5115_;
v___y_5000_ = v___y_5117_;
v___y_5001_ = v___y_5116_;
v___y_5002_ = v_a_5121_;
v___y_5003_ = v___y_5118_;
v___y_5004_ = v___x_5134_;
v___y_5005_ = v___x_5142_;
goto v___jp_4994_;
}
}
else
{
lean_object* v_a_5143_; 
lean_dec(v___y_5110_);
v_a_5143_ = lean_ctor_get(v___x_5135_, 0);
lean_inc(v_a_5143_);
lean_dec_ref_known(v___x_5135_, 1);
v___y_4931_ = v___y_5112_;
v___y_4932_ = v___y_5113_;
v___y_4933_ = v___y_5115_;
v___y_4934_ = v_a_5121_;
v___y_4935_ = v___y_5118_;
v___y_4936_ = v___x_5134_;
v_a_4937_ = v_a_5143_;
goto v___jp_4930_;
}
}
}
v___jp_5144_:
{
lean_object* v_toCold_5148_; lean_object* v_options_5149_; lean_object* v_inheritedTraceOptions_5150_; uint8_t v_hasTrace_5151_; lean_object* v___x_5152_; size_t v_sz_5153_; size_t v___x_5154_; 
v_toCold_5148_ = lean_ctor_get(v_a_4815_, 0);
v_options_5149_ = lean_ctor_get(v_toCold_5148_, 2);
v_inheritedTraceOptions_5150_ = lean_ctor_get(v_toCold_5148_, 11);
v_hasTrace_5151_ = lean_ctor_get_uint8(v_options_5149_, sizeof(void*)*1);
v___x_5152_ = lean_box(0);
v_sz_5153_ = lean_array_size(v___y_5147_);
v___x_5154_ = ((size_t)0ULL);
if (v_hasTrace_5151_ == 0)
{
lean_object* v___x_5155_; 
v___x_5155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7(v___y_5147_, v_sz_5153_, v___x_5154_, v___x_5152_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
lean_dec_ref(v___y_5147_);
if (lean_obj_tag(v___x_5155_) == 0)
{
lean_object* v_size_5156_; lean_object* v_buckets_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; uint8_t v___x_5160_; 
lean_dec_ref_known(v___x_5155_, 1);
v_size_5156_ = lean_ctor_get(v_predInfo_4819_, 0);
v_buckets_5157_ = lean_ctor_get(v_predInfo_4819_, 1);
v___x_5158_ = lean_mk_empty_array_with_capacity(v_size_5156_);
v___x_5159_ = lean_array_get_size(v_buckets_5157_);
v___x_5160_ = lean_nat_dec_lt(v___y_5145_, v___x_5159_);
if (v___x_5160_ == 0)
{
v___y_4857_ = v___y_5145_;
v___y_4858_ = v___x_5154_;
v___y_4859_ = v___x_5152_;
v___y_4860_ = v___y_5146_;
v___y_4861_ = v___x_5158_;
goto v___jp_4856_;
}
else
{
size_t v___x_5161_; lean_object* v___x_5162_; 
v___x_5161_ = lean_usize_of_nat(v___x_5159_);
v___x_5162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13(v_buckets_5157_, v___x_5154_, v___x_5161_, v___x_5158_);
v___y_4857_ = v___y_5145_;
v___y_4858_ = v___x_5154_;
v___y_4859_ = v___x_5152_;
v___y_4860_ = v___y_5146_;
v___y_4861_ = v___x_5162_;
goto v___jp_4856_;
}
}
else
{
lean_dec(v___y_5145_);
return v___x_5155_;
}
}
else
{
lean_object* v___x_5163_; lean_object* v___x_5164_; uint8_t v___x_5165_; 
v___x_5163_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__1));
v___x_5164_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9);
v___x_5165_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5150_, v_options_5149_, v___x_5164_);
if (v___x_5165_ == 0)
{
lean_object* v___x_5166_; uint8_t v___x_5167_; 
v___x_5166_ = l_Lean_trace_profiler;
v___x_5167_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15(v_options_5149_, v___x_5166_);
if (v___x_5167_ == 0)
{
lean_object* v___x_5168_; 
v___x_5168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7(v___y_5147_, v_sz_5153_, v___x_5154_, v___x_5152_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
lean_dec_ref(v___y_5147_);
if (lean_obj_tag(v___x_5168_) == 0)
{
lean_object* v_size_5169_; lean_object* v_buckets_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; uint8_t v___x_5173_; 
lean_dec_ref_known(v___x_5168_, 1);
v_size_5169_ = lean_ctor_get(v_predInfo_4819_, 0);
v_buckets_5170_ = lean_ctor_get(v_predInfo_4819_, 1);
v___x_5171_ = lean_mk_empty_array_with_capacity(v_size_5169_);
v___x_5172_ = lean_array_get_size(v_buckets_5170_);
v___x_5173_ = lean_nat_dec_lt(v___y_5145_, v___x_5172_);
if (v___x_5173_ == 0)
{
v___y_4901_ = v___y_5145_;
v___y_4902_ = v___x_5154_;
v___y_4903_ = v___x_5152_;
v___y_4904_ = v___y_5146_;
v___y_4905_ = v___x_5171_;
goto v___jp_4900_;
}
else
{
size_t v___x_5174_; lean_object* v___x_5175_; 
v___x_5174_ = lean_usize_of_nat(v___x_5172_);
v___x_5175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13(v_buckets_5170_, v___x_5154_, v___x_5174_, v___x_5171_);
v___y_4901_ = v___y_5145_;
v___y_4902_ = v___x_5154_;
v___y_4903_ = v___x_5152_;
v___y_4904_ = v___y_5146_;
v___y_4905_ = v___x_5175_;
goto v___jp_4900_;
}
}
else
{
lean_dec(v___y_5145_);
return v___x_5168_;
}
}
else
{
v___y_5110_ = v___y_5145_;
v___y_5111_ = v_sz_5153_;
v___y_5112_ = v_hasTrace_5151_;
v___y_5113_ = v___x_5165_;
v___y_5114_ = v___x_5154_;
v___y_5115_ = v_options_5149_;
v___y_5116_ = v___y_5146_;
v___y_5117_ = v___x_5152_;
v___y_5118_ = v___x_5163_;
v___y_5119_ = v___y_5147_;
goto v___jp_5109_;
}
}
else
{
v___y_5110_ = v___y_5145_;
v___y_5111_ = v_sz_5153_;
v___y_5112_ = v_hasTrace_5151_;
v___y_5113_ = v___x_5165_;
v___y_5114_ = v___x_5154_;
v___y_5115_ = v_options_5149_;
v___y_5116_ = v___y_5146_;
v___y_5117_ = v___x_5152_;
v___y_5118_ = v___x_5163_;
v___y_5119_ = v___y_5147_;
goto v___jp_5109_;
}
}
}
v___jp_5176_:
{
lean_object* v___x_5183_; 
v___x_5183_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg(v___y_5178_, v___y_5181_, v___y_5180_, v___y_5182_);
lean_dec(v___y_5182_);
lean_dec(v___y_5178_);
v___y_5145_ = v___y_5177_;
v___y_5146_ = v___y_5179_;
v___y_5147_ = v___x_5183_;
goto v___jp_5144_;
}
v___jp_5184_:
{
uint8_t v___x_5191_; 
v___x_5191_ = lean_nat_dec_le(v___y_5190_, v___y_5185_);
if (v___x_5191_ == 0)
{
lean_dec(v___y_5185_);
lean_inc(v___y_5190_);
v___y_5177_ = v___y_5186_;
v___y_5178_ = v___y_5187_;
v___y_5179_ = v___y_5188_;
v___y_5180_ = v___y_5190_;
v___y_5181_ = v___y_5189_;
v___y_5182_ = v___y_5190_;
goto v___jp_5176_;
}
else
{
v___y_5177_ = v___y_5186_;
v___y_5178_ = v___y_5187_;
v___y_5179_ = v___y_5188_;
v___y_5180_ = v___y_5190_;
v___y_5181_ = v___y_5189_;
v___y_5182_ = v___y_5185_;
goto v___jp_5176_;
}
}
v___jp_5192_:
{
lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; uint8_t v___x_5197_; 
v___x_5194_ = lean_unsigned_to_nat(0u);
v___x_5195_ = lean_unsigned_to_nat(1u);
v___x_5196_ = lean_array_get_size(v___y_5193_);
v___x_5197_ = lean_nat_dec_eq(v___x_5196_, v___x_5194_);
if (v___x_5197_ == 0)
{
lean_object* v___x_5198_; uint8_t v___x_5199_; 
v___x_5198_ = lean_nat_sub(v___x_5196_, v___x_5195_);
v___x_5199_ = lean_nat_dec_le(v___x_5194_, v___x_5198_);
if (v___x_5199_ == 0)
{
lean_inc(v___x_5198_);
v___y_5185_ = v___x_5198_;
v___y_5186_ = v___x_5194_;
v___y_5187_ = v___x_5196_;
v___y_5188_ = v___x_5195_;
v___y_5189_ = v___y_5193_;
v___y_5190_ = v___x_5198_;
goto v___jp_5184_;
}
else
{
v___y_5185_ = v___x_5198_;
v___y_5186_ = v___x_5194_;
v___y_5187_ = v___x_5196_;
v___y_5188_ = v___x_5195_;
v___y_5189_ = v___y_5193_;
v___y_5190_ = v___x_5194_;
goto v___jp_5184_;
}
}
else
{
v___y_5145_ = v___x_5194_;
v___y_5146_ = v___x_5195_;
v___y_5147_ = v___y_5193_;
goto v___jp_5144_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___boxed(lean_object* v_problem_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_){
_start:
{
lean_object* v_res_5213_; 
v_res_5213_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem(v_problem_5207_, v_a_5208_, v_a_5209_, v_a_5210_, v_a_5211_);
lean_dec(v_a_5211_);
lean_dec_ref(v_a_5210_);
lean_dec(v_a_5209_);
lean_dec_ref(v_a_5208_);
lean_dec_ref(v_problem_5207_);
return v_res_5213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11(lean_object* v_n_5214_, lean_object* v_as_5215_, lean_object* v_lo_5216_, lean_object* v_hi_5217_, lean_object* v_w_5218_, lean_object* v_hlo_5219_, lean_object* v_hhi_5220_){
_start:
{
lean_object* v___x_5221_; 
v___x_5221_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v_n_5214_, v_as_5215_, v_lo_5216_, v_hi_5217_);
return v___x_5221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___boxed(lean_object* v_n_5222_, lean_object* v_as_5223_, lean_object* v_lo_5224_, lean_object* v_hi_5225_, lean_object* v_w_5226_, lean_object* v_hlo_5227_, lean_object* v_hhi_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11(v_n_5222_, v_as_5223_, v_lo_5224_, v_hi_5225_, v_w_5226_, v_hlo_5227_, v_hhi_5228_);
lean_dec(v_hi_5225_);
lean_dec(v_n_5222_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19(lean_object* v_00_u03b1_5230_, lean_object* v_x_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_){
_start:
{
lean_object* v___x_5237_; 
v___x_5237_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg(v_x_5231_);
return v___x_5237_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___boxed(lean_object* v_00_u03b1_5238_, lean_object* v_x_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
lean_object* v_res_5245_; 
v_res_5245_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19(v_00_u03b1_5238_, v_x_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
lean_dec(v___y_5243_);
lean_dec_ref(v___y_5242_);
lean_dec(v___y_5241_);
lean_dec_ref(v___y_5240_);
return v_res_5245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17(lean_object* v_n_5246_, lean_object* v_as_5247_, lean_object* v_lo_5248_, lean_object* v_hi_5249_, lean_object* v_w_5250_, lean_object* v_hlo_5251_, lean_object* v_hhi_5252_){
_start:
{
lean_object* v___x_5253_; 
v___x_5253_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg(v_n_5246_, v_as_5247_, v_lo_5248_, v_hi_5249_);
return v___x_5253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___boxed(lean_object* v_n_5254_, lean_object* v_as_5255_, lean_object* v_lo_5256_, lean_object* v_hi_5257_, lean_object* v_w_5258_, lean_object* v_hlo_5259_, lean_object* v_hhi_5260_){
_start:
{
lean_object* v_res_5261_; 
v_res_5261_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17(v_n_5254_, v_as_5255_, v_lo_5256_, v_hi_5257_, v_w_5258_, v_hlo_5259_, v_hhi_5260_);
lean_dec(v_hi_5257_);
lean_dec(v_n_5254_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12(lean_object* v_n_5262_, lean_object* v_lo_5263_, lean_object* v_hi_5264_, lean_object* v_hhi_5265_, lean_object* v_pivot_5266_, lean_object* v_as_5267_, lean_object* v_i_5268_, lean_object* v_k_5269_, lean_object* v_ilo_5270_, lean_object* v_ik_5271_, lean_object* v_w_5272_){
_start:
{
lean_object* v___x_5273_; 
v___x_5273_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___redArg(v_hi_5264_, v_pivot_5266_, v_as_5267_, v_i_5268_, v_k_5269_);
return v___x_5273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___boxed(lean_object* v_n_5274_, lean_object* v_lo_5275_, lean_object* v_hi_5276_, lean_object* v_hhi_5277_, lean_object* v_pivot_5278_, lean_object* v_as_5279_, lean_object* v_i_5280_, lean_object* v_k_5281_, lean_object* v_ilo_5282_, lean_object* v_ik_5283_, lean_object* v_w_5284_){
_start:
{
lean_object* v_res_5285_; 
v_res_5285_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12(v_n_5274_, v_lo_5275_, v_hi_5276_, v_hhi_5277_, v_pivot_5278_, v_as_5279_, v_i_5280_, v_k_5281_, v_ilo_5282_, v_ik_5283_, v_w_5284_);
lean_dec_ref(v_pivot_5278_);
lean_dec(v_hi_5276_);
lean_dec(v_lo_5275_);
lean_dec(v_n_5274_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23(lean_object* v_n_5286_, lean_object* v_lo_5287_, lean_object* v_hi_5288_, lean_object* v_hhi_5289_, lean_object* v_pivot_5290_, lean_object* v_as_5291_, lean_object* v_i_5292_, lean_object* v_k_5293_, lean_object* v_ilo_5294_, lean_object* v_ik_5295_, lean_object* v_w_5296_){
_start:
{
lean_object* v___x_5297_; 
v___x_5297_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___redArg(v_hi_5288_, v_pivot_5290_, v_as_5291_, v_i_5292_, v_k_5293_);
return v___x_5297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___boxed(lean_object* v_n_5298_, lean_object* v_lo_5299_, lean_object* v_hi_5300_, lean_object* v_hhi_5301_, lean_object* v_pivot_5302_, lean_object* v_as_5303_, lean_object* v_i_5304_, lean_object* v_k_5305_, lean_object* v_ilo_5306_, lean_object* v_ik_5307_, lean_object* v_w_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23(v_n_5298_, v_lo_5299_, v_hi_5300_, v_hhi_5301_, v_pivot_5302_, v_as_5303_, v_i_5304_, v_k_5305_, v_ilo_5306_, v_ik_5307_, v_w_5308_);
lean_dec_ref(v_pivot_5302_);
lean_dec(v_hi_5300_);
lean_dec(v_lo_5299_);
lean_dec(v_n_5298_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg___lam__0(lean_object* v_x_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_){
_start:
{
lean_object* v___x_5318_; 
lean_inc(v___y_5312_);
lean_inc_ref(v___y_5311_);
v___x_5318_ = lean_apply_7(v_x_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, lean_box(0));
return v___x_5318_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg___lam__0___boxed(lean_object* v_x_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_){
_start:
{
lean_object* v_res_5327_; 
v_res_5327_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg___lam__0(v_x_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_);
lean_dec(v___y_5321_);
lean_dec_ref(v___y_5320_);
return v_res_5327_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg(lean_object* v_mvarId_5328_, lean_object* v_x_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_){
_start:
{
lean_object* v___f_5337_; lean_object* v___x_5338_; 
lean_inc(v___y_5331_);
lean_inc_ref(v___y_5330_);
v___f_5337_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_5337_, 0, v_x_5329_);
lean_closure_set(v___f_5337_, 1, v___y_5330_);
lean_closure_set(v___f_5337_, 2, v___y_5331_);
v___x_5338_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5328_, v___f_5337_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_);
if (lean_obj_tag(v___x_5338_) == 0)
{
return v___x_5338_;
}
else
{
lean_object* v_a_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5346_; 
v_a_5339_ = lean_ctor_get(v___x_5338_, 0);
v_isSharedCheck_5346_ = !lean_is_exclusive(v___x_5338_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5341_ = v___x_5338_;
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_a_5339_);
lean_dec(v___x_5338_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5344_; 
if (v_isShared_5342_ == 0)
{
v___x_5344_ = v___x_5341_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_a_5339_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg___boxed(lean_object* v_mvarId_5347_, lean_object* v_x_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_){
_start:
{
lean_object* v_res_5356_; 
v_res_5356_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg(v_mvarId_5347_, v_x_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_);
lean_dec(v___y_5354_);
lean_dec_ref(v___y_5353_);
lean_dec(v___y_5352_);
lean_dec_ref(v___y_5351_);
lean_dec(v___y_5350_);
lean_dec_ref(v___y_5349_);
return v_res_5356_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0(lean_object* v_00_u03b1_5357_, lean_object* v_mvarId_5358_, lean_object* v_x_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v___x_5367_; 
v___x_5367_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg(v_mvarId_5358_, v_x_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
return v___x_5367_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___boxed(lean_object* v_00_u03b1_5368_, lean_object* v_mvarId_5369_, lean_object* v_x_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_){
_start:
{
lean_object* v_res_5378_; 
v_res_5378_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0(v_00_u03b1_5368_, v_mvarId_5369_, v_x_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_);
lean_dec(v___y_5376_);
lean_dec_ref(v___y_5375_);
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
return v_res_5378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode___lam__0(lean_object* v_hyps_5379_, lean_object* v_g_5380_, uint8_t v_symBreak_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_){
_start:
{
lean_object* v___x_5389_; 
v___x_5389_ = l_Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem(v_hyps_5379_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_);
if (lean_obj_tag(v___x_5389_) == 0)
{
lean_object* v_a_5390_; lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5452_; 
v_a_5390_ = lean_ctor_get(v___x_5389_, 0);
v_isSharedCheck_5452_ = !lean_is_exclusive(v___x_5389_);
if (v_isSharedCheck_5452_ == 0)
{
v___x_5392_ = v___x_5389_;
v_isShared_5393_ = v_isSharedCheck_5452_;
goto v_resetjp_5391_;
}
else
{
lean_inc(v_a_5390_);
lean_dec(v___x_5389_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5452_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v_problem_5394_; lean_object* v_remainingHyps_5395_; lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5451_; 
v_problem_5394_ = lean_ctor_get(v_a_5390_, 0);
v_remainingHyps_5395_ = lean_ctor_get(v_a_5390_, 1);
v_isSharedCheck_5451_ = !lean_is_exclusive(v_a_5390_);
if (v_isSharedCheck_5451_ == 0)
{
v___x_5397_ = v_a_5390_;
v_isShared_5398_ = v_isSharedCheck_5451_;
goto v_resetjp_5396_;
}
else
{
lean_inc(v_remainingHyps_5395_);
lean_inc(v_problem_5394_);
lean_dec(v_a_5390_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5451_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
lean_object* v_groundFacts_5440_; lean_object* v_quantifiedFacts_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; uint8_t v___x_5444_; 
v_groundFacts_5440_ = lean_ctor_get(v_problem_5394_, 3);
v_quantifiedFacts_5441_ = lean_ctor_get(v_problem_5394_, 4);
v___x_5442_ = lean_array_get_size(v_groundFacts_5440_);
v___x_5443_ = lean_unsigned_to_nat(0u);
v___x_5444_ = lean_nat_dec_eq(v___x_5442_, v___x_5443_);
if (v___x_5444_ == 0)
{
lean_del_object(v___x_5392_);
goto v___jp_5399_;
}
else
{
lean_object* v___x_5445_; uint8_t v___x_5446_; 
v___x_5445_ = lean_array_get_size(v_quantifiedFacts_5441_);
v___x_5446_ = lean_nat_dec_eq(v___x_5445_, v___x_5443_);
if (v___x_5446_ == 0)
{
lean_del_object(v___x_5392_);
goto v___jp_5399_;
}
else
{
lean_object* v___x_5447_; lean_object* v___x_5449_; 
lean_del_object(v___x_5397_);
lean_dec_ref(v_remainingHyps_5395_);
lean_dec_ref(v_problem_5394_);
lean_dec(v_g_5380_);
v___x_5447_ = lean_box(0);
if (v_isShared_5393_ == 0)
{
lean_ctor_set(v___x_5392_, 0, v___x_5447_);
v___x_5449_ = v___x_5392_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5450_; 
v_reuseFailAlloc_5450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5450_, 0, v___x_5447_);
v___x_5449_ = v_reuseFailAlloc_5450_;
goto v_reusejp_5448_;
}
v_reusejp_5448_:
{
return v___x_5449_;
}
}
}
v___jp_5399_:
{
lean_object* v___x_5400_; 
v___x_5400_ = l_Lean_Meta_Tactic_BVDecide_EPR_EprProblem_inferSorts(v_problem_5394_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_);
if (lean_obj_tag(v___x_5400_) == 0)
{
lean_object* v_a_5401_; lean_object* v___x_5402_; 
v_a_5401_ = lean_ctor_get(v___x_5400_, 0);
lean_inc(v_a_5401_);
lean_dec_ref_known(v___x_5400_, 1);
v___x_5402_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem(v_a_5401_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_);
if (lean_obj_tag(v___x_5402_) == 0)
{
lean_object* v___x_5403_; 
lean_dec_ref_known(v___x_5402_, 1);
v___x_5403_ = l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec(v_a_5401_, v_g_5380_, v_symBreak_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_);
if (lean_obj_tag(v___x_5403_) == 0)
{
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5415_; 
v_a_5404_ = lean_ctor_get(v___x_5403_, 0);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5403_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5406_ = v___x_5403_;
v_isShared_5407_ = v_isSharedCheck_5415_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___x_5403_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5415_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5409_; 
if (v_isShared_5398_ == 0)
{
lean_ctor_set(v___x_5397_, 1, v_a_5404_);
lean_ctor_set(v___x_5397_, 0, v_remainingHyps_5395_);
v___x_5409_ = v___x_5397_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_remainingHyps_5395_);
lean_ctor_set(v_reuseFailAlloc_5414_, 1, v_a_5404_);
v___x_5409_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
lean_object* v___x_5410_; lean_object* v___x_5412_; 
v___x_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5410_, 0, v___x_5409_);
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 0, v___x_5410_);
v___x_5412_ = v___x_5406_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v___x_5410_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
return v___x_5412_;
}
}
}
}
else
{
lean_object* v_a_5416_; lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5423_; 
lean_del_object(v___x_5397_);
lean_dec_ref(v_remainingHyps_5395_);
v_a_5416_ = lean_ctor_get(v___x_5403_, 0);
v_isSharedCheck_5423_ = !lean_is_exclusive(v___x_5403_);
if (v_isSharedCheck_5423_ == 0)
{
v___x_5418_ = v___x_5403_;
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
else
{
lean_inc(v_a_5416_);
lean_dec(v___x_5403_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
lean_object* v___x_5421_; 
if (v_isShared_5419_ == 0)
{
v___x_5421_ = v___x_5418_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_a_5416_);
v___x_5421_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
return v___x_5421_;
}
}
}
}
else
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5431_; 
lean_dec(v_a_5401_);
lean_del_object(v___x_5397_);
lean_dec_ref(v_remainingHyps_5395_);
lean_dec(v_g_5380_);
v_a_5424_ = lean_ctor_get(v___x_5402_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5402_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5426_ = v___x_5402_;
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5402_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
v___x_5429_ = v___x_5426_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
v___x_5429_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
return v___x_5429_;
}
}
}
}
else
{
lean_object* v_a_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5439_; 
lean_del_object(v___x_5397_);
lean_dec_ref(v_remainingHyps_5395_);
lean_dec(v_g_5380_);
v_a_5432_ = lean_ctor_get(v___x_5400_, 0);
v_isSharedCheck_5439_ = !lean_is_exclusive(v___x_5400_);
if (v_isSharedCheck_5439_ == 0)
{
v___x_5434_ = v___x_5400_;
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_a_5432_);
lean_dec(v___x_5400_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
lean_object* v___x_5437_; 
if (v_isShared_5435_ == 0)
{
v___x_5437_ = v___x_5434_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_a_5432_);
v___x_5437_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
return v___x_5437_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5453_; lean_object* v___x_5455_; uint8_t v_isShared_5456_; uint8_t v_isSharedCheck_5460_; 
lean_dec(v_g_5380_);
v_a_5453_ = lean_ctor_get(v___x_5389_, 0);
v_isSharedCheck_5460_ = !lean_is_exclusive(v___x_5389_);
if (v_isSharedCheck_5460_ == 0)
{
v___x_5455_ = v___x_5389_;
v_isShared_5456_ = v_isSharedCheck_5460_;
goto v_resetjp_5454_;
}
else
{
lean_inc(v_a_5453_);
lean_dec(v___x_5389_);
v___x_5455_ = lean_box(0);
v_isShared_5456_ = v_isSharedCheck_5460_;
goto v_resetjp_5454_;
}
v_resetjp_5454_:
{
lean_object* v___x_5458_; 
if (v_isShared_5456_ == 0)
{
v___x_5458_ = v___x_5455_;
goto v_reusejp_5457_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_a_5453_);
v___x_5458_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5457_;
}
v_reusejp_5457_:
{
return v___x_5458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode___lam__0___boxed(lean_object* v_hyps_5461_, lean_object* v_g_5462_, lean_object* v_symBreak_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_){
_start:
{
uint8_t v_symBreak_boxed_5471_; lean_object* v_res_5472_; 
v_symBreak_boxed_5471_ = lean_unbox(v_symBreak_5463_);
v_res_5472_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode___lam__0(v_hyps_5461_, v_g_5462_, v_symBreak_boxed_5471_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_);
lean_dec(v___y_5469_);
lean_dec_ref(v___y_5468_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
lean_dec(v___y_5465_);
lean_dec_ref(v___y_5464_);
lean_dec_ref(v_hyps_5461_);
return v_res_5472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode(lean_object* v_g_5473_, lean_object* v_hyps_5474_, uint8_t v_symBreak_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_){
_start:
{
lean_object* v___x_5483_; lean_object* v___f_5484_; lean_object* v___x_5485_; 
v___x_5483_ = lean_box(v_symBreak_5475_);
lean_inc(v_g_5473_);
v___f_5484_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5484_, 0, v_hyps_5474_);
lean_closure_set(v___f_5484_, 1, v_g_5473_);
lean_closure_set(v___f_5484_, 2, v___x_5483_);
v___x_5485_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg(v_g_5473_, v___f_5484_, v_a_5476_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_);
return v___x_5485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode___boxed(lean_object* v_g_5486_, lean_object* v_hyps_5487_, lean_object* v_symBreak_5488_, lean_object* v_a_5489_, lean_object* v_a_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_){
_start:
{
uint8_t v_symBreak_boxed_5496_; lean_object* v_res_5497_; 
v_symBreak_boxed_5496_ = lean_unbox(v_symBreak_5488_);
v_res_5497_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode(v_g_5486_, v_hyps_5487_, v_symBreak_boxed_5496_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_, v_a_5493_, v_a_5494_);
lean_dec(v_a_5494_);
lean_dec_ref(v_a_5493_);
lean_dec(v_a_5492_);
lean_dec_ref(v_a_5491_);
lean_dec(v_a_5490_);
lean_dec_ref(v_a_5489_);
return v_res_5497_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___redArg(lean_object* v_cls_5498_, lean_object* v_msg_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_){
_start:
{
lean_object* v_ref_5505_; lean_object* v___x_5506_; lean_object* v_a_5507_; lean_object* v___x_5509_; uint8_t v_isShared_5510_; uint8_t v_isSharedCheck_5552_; 
v_ref_5505_ = lean_ctor_get(v___y_5502_, 2);
v___x_5506_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2_spec__3(v_msg_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_);
v_a_5507_ = lean_ctor_get(v___x_5506_, 0);
v_isSharedCheck_5552_ = !lean_is_exclusive(v___x_5506_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5509_ = v___x_5506_;
v_isShared_5510_ = v_isSharedCheck_5552_;
goto v_resetjp_5508_;
}
else
{
lean_inc(v_a_5507_);
lean_dec(v___x_5506_);
v___x_5509_ = lean_box(0);
v_isShared_5510_ = v_isSharedCheck_5552_;
goto v_resetjp_5508_;
}
v_resetjp_5508_:
{
lean_object* v___x_5511_; lean_object* v_traceState_5512_; lean_object* v_env_5513_; lean_object* v_nextMacroScope_5514_; lean_object* v_ngen_5515_; lean_object* v_auxDeclNGen_5516_; lean_object* v_cache_5517_; lean_object* v_recordedDeps_5518_; lean_object* v_messages_5519_; lean_object* v_infoState_5520_; lean_object* v_snapshotTasks_5521_; lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5551_; 
v___x_5511_ = lean_st_ref_take(v___y_5503_);
v_traceState_5512_ = lean_ctor_get(v___x_5511_, 4);
v_env_5513_ = lean_ctor_get(v___x_5511_, 0);
v_nextMacroScope_5514_ = lean_ctor_get(v___x_5511_, 1);
v_ngen_5515_ = lean_ctor_get(v___x_5511_, 2);
v_auxDeclNGen_5516_ = lean_ctor_get(v___x_5511_, 3);
v_cache_5517_ = lean_ctor_get(v___x_5511_, 5);
v_recordedDeps_5518_ = lean_ctor_get(v___x_5511_, 6);
v_messages_5519_ = lean_ctor_get(v___x_5511_, 7);
v_infoState_5520_ = lean_ctor_get(v___x_5511_, 8);
v_snapshotTasks_5521_ = lean_ctor_get(v___x_5511_, 9);
v_isSharedCheck_5551_ = !lean_is_exclusive(v___x_5511_);
if (v_isSharedCheck_5551_ == 0)
{
v___x_5523_ = v___x_5511_;
v_isShared_5524_ = v_isSharedCheck_5551_;
goto v_resetjp_5522_;
}
else
{
lean_inc(v_snapshotTasks_5521_);
lean_inc(v_infoState_5520_);
lean_inc(v_messages_5519_);
lean_inc(v_recordedDeps_5518_);
lean_inc(v_cache_5517_);
lean_inc(v_traceState_5512_);
lean_inc(v_auxDeclNGen_5516_);
lean_inc(v_ngen_5515_);
lean_inc(v_nextMacroScope_5514_);
lean_inc(v_env_5513_);
lean_dec(v___x_5511_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5551_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
uint64_t v_tid_5525_; lean_object* v_traces_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5550_; 
v_tid_5525_ = lean_ctor_get_uint64(v_traceState_5512_, sizeof(void*)*1);
v_traces_5526_ = lean_ctor_get(v_traceState_5512_, 0);
v_isSharedCheck_5550_ = !lean_is_exclusive(v_traceState_5512_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5528_ = v_traceState_5512_;
v_isShared_5529_ = v_isSharedCheck_5550_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_traces_5526_);
lean_dec(v_traceState_5512_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5550_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v___x_5530_; lean_object* v___x_5531_; double v___x_5532_; uint8_t v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5541_; 
v___x_5530_ = lean_box(0);
v___x_5531_ = lean_box(0);
v___x_5532_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__0);
v___x_5533_ = 0;
v___x_5534_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__1));
v___x_5535_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5535_, 0, v_cls_5498_);
lean_ctor_set(v___x_5535_, 1, v___x_5531_);
lean_ctor_set(v___x_5535_, 2, v___x_5534_);
lean_ctor_set_float(v___x_5535_, sizeof(void*)*3, v___x_5532_);
lean_ctor_set_float(v___x_5535_, sizeof(void*)*3 + 8, v___x_5532_);
lean_ctor_set_uint8(v___x_5535_, sizeof(void*)*3 + 16, v___x_5533_);
v___x_5536_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___redArg___closed__2));
v___x_5537_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5537_, 0, v___x_5535_);
lean_ctor_set(v___x_5537_, 1, v_a_5507_);
lean_ctor_set(v___x_5537_, 2, v___x_5536_);
lean_inc(v_ref_5505_);
v___x_5538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5538_, 0, v_ref_5505_);
lean_ctor_set(v___x_5538_, 1, v___x_5537_);
v___x_5539_ = l_Lean_PersistentArray_push___redArg(v_traces_5526_, v___x_5538_);
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 0, v___x_5539_);
v___x_5541_ = v___x_5528_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v___x_5539_);
lean_ctor_set_uint64(v_reuseFailAlloc_5549_, sizeof(void*)*1, v_tid_5525_);
v___x_5541_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
lean_object* v___x_5543_; 
if (v_isShared_5524_ == 0)
{
lean_ctor_set(v___x_5523_, 4, v___x_5541_);
v___x_5543_ = v___x_5523_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_env_5513_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v_nextMacroScope_5514_);
lean_ctor_set(v_reuseFailAlloc_5548_, 2, v_ngen_5515_);
lean_ctor_set(v_reuseFailAlloc_5548_, 3, v_auxDeclNGen_5516_);
lean_ctor_set(v_reuseFailAlloc_5548_, 4, v___x_5541_);
lean_ctor_set(v_reuseFailAlloc_5548_, 5, v_cache_5517_);
lean_ctor_set(v_reuseFailAlloc_5548_, 6, v_recordedDeps_5518_);
lean_ctor_set(v_reuseFailAlloc_5548_, 7, v_messages_5519_);
lean_ctor_set(v_reuseFailAlloc_5548_, 8, v_infoState_5520_);
lean_ctor_set(v_reuseFailAlloc_5548_, 9, v_snapshotTasks_5521_);
v___x_5543_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
lean_object* v___x_5544_; lean_object* v___x_5546_; 
v___x_5544_ = lean_st_ref_put(v___y_5503_, v___x_5543_);
if (v_isShared_5510_ == 0)
{
lean_ctor_set(v___x_5509_, 0, v___x_5530_);
v___x_5546_ = v___x_5509_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v___x_5530_);
v___x_5546_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
return v___x_5546_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___redArg___boxed(lean_object* v_cls_5553_, lean_object* v_msg_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_){
_start:
{
lean_object* v_res_5560_; 
v_res_5560_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___redArg(v_cls_5553_, v_msg_5554_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_);
lean_dec(v___y_5558_);
lean_dec_ref(v___y_5557_);
lean_dec(v___y_5556_);
lean_dec_ref(v___y_5555_);
return v_res_5560_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__1(void){
_start:
{
lean_object* v_cls_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; 
v_cls_5565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__0));
v___x_5566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__8));
v___x_5567_ = l_Lean_Name_append(v___x_5566_, v_cls_5565_);
return v___x_5567_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__3(void){
_start:
{
lean_object* v___x_5569_; lean_object* v___x_5570_; 
v___x_5569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__2));
v___x_5570_ = l_Lean_stringToMessageData(v___x_5569_);
return v___x_5570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1(lean_object* v_as_5571_, size_t v_i_5572_, size_t v_stop_5573_, lean_object* v_b_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_){
_start:
{
lean_object* v_a_5588_; uint8_t v___x_5594_; 
v___x_5594_ = lean_usize_dec_eq(v_i_5572_, v_stop_5573_);
if (v___x_5594_ == 0)
{
lean_object* v_toCold_5595_; lean_object* v_options_5596_; uint8_t v_hasTrace_5597_; 
v_toCold_5595_ = lean_ctor_get(v___y_5584_, 0);
v_options_5596_ = lean_ctor_get(v_toCold_5595_, 2);
v_hasTrace_5597_ = lean_ctor_get_uint8(v_options_5596_, sizeof(void*)*1);
if (v_hasTrace_5597_ == 0)
{
goto v___jp_5592_;
}
else
{
lean_object* v_inheritedTraceOptions_5598_; lean_object* v_cls_5599_; lean_object* v___x_5600_; uint8_t v___x_5601_; 
v_inheritedTraceOptions_5598_ = lean_ctor_get(v_toCold_5595_, 11);
v_cls_5599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__0));
v___x_5600_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__1);
v___x_5601_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5598_, v_options_5596_, v___x_5600_);
if (v___x_5601_ == 0)
{
goto v___jp_5592_;
}
else
{
lean_object* v___x_5602_; lean_object* v_type_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; 
v___x_5602_ = lean_array_uget_borrowed(v_as_5571_, v_i_5572_);
v_type_5603_ = lean_ctor_get(v___x_5602_, 1);
v___x_5604_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__3);
lean_inc_ref(v_type_5603_);
v___x_5605_ = l_Lean_MessageData_ofExpr(v_type_5603_);
v___x_5606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5606_, 0, v___x_5604_);
lean_ctor_set(v___x_5606_, 1, v___x_5605_);
v___x_5607_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___redArg(v_cls_5599_, v___x_5606_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_);
if (lean_obj_tag(v___x_5607_) == 0)
{
lean_object* v_a_5608_; 
v_a_5608_ = lean_ctor_get(v___x_5607_, 0);
lean_inc(v_a_5608_);
lean_dec_ref_known(v___x_5607_, 1);
v_a_5588_ = v_a_5608_;
goto v___jp_5587_;
}
else
{
return v___x_5607_;
}
}
}
}
else
{
lean_object* v___x_5609_; 
v___x_5609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5609_, 0, v_b_5574_);
return v___x_5609_;
}
v___jp_5587_:
{
size_t v___x_5589_; size_t v___x_5590_; 
v___x_5589_ = ((size_t)1ULL);
v___x_5590_ = lean_usize_add(v_i_5572_, v___x_5589_);
v_i_5572_ = v___x_5590_;
v_b_5574_ = v_a_5588_;
goto _start;
}
v___jp_5592_:
{
lean_object* v___x_5593_; 
v___x_5593_ = lean_box(0);
v_a_5588_ = v___x_5593_;
goto v___jp_5587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___boxed(lean_object* v_as_5610_, lean_object* v_i_5611_, lean_object* v_stop_5612_, lean_object* v_b_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_){
_start:
{
size_t v_i_boxed_5626_; size_t v_stop_boxed_5627_; lean_object* v_res_5628_; 
v_i_boxed_5626_ = lean_unbox_usize(v_i_5611_);
lean_dec(v_i_5611_);
v_stop_boxed_5627_ = lean_unbox_usize(v_stop_5612_);
lean_dec(v_stop_5612_);
v_res_5628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1(v_as_5610_, v_i_boxed_5626_, v_stop_boxed_5627_, v_b_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_);
lean_dec(v___y_5624_);
lean_dec_ref(v___y_5623_);
lean_dec(v___y_5622_);
lean_dec_ref(v___y_5621_);
lean_dec(v___y_5620_);
lean_dec_ref(v___y_5619_);
lean_dec(v___y_5618_);
lean_dec_ref(v___y_5617_);
lean_dec(v___y_5616_);
lean_dec(v___y_5615_);
lean_dec_ref(v___y_5614_);
lean_dec_ref(v_as_5610_);
return v_res_5628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___lam__0(lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_){
_start:
{
lean_object* v___x_5641_; lean_object* v_config_5642_; lean_object* v_target_5643_; uint8_t v_eprSymBreak_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v_hypotheses_5647_; lean_object* v___x_5648_; 
v___x_5641_ = lean_st_ref_get(v___y_5630_);
v_config_5642_ = lean_ctor_get(v___y_5629_, 0);
v_target_5643_ = lean_ctor_get(v___x_5641_, 2);
lean_inc_ref(v_target_5643_);
lean_dec(v___x_5641_);
v_eprSymBreak_5644_ = lean_ctor_get_uint8(v_config_5642_, sizeof(void*)*3 + 13);
v___x_5645_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_5643_);
lean_dec_ref(v_target_5643_);
v___x_5646_ = lean_st_ref_get(v___y_5630_);
v_hypotheses_5647_ = lean_ctor_get(v___x_5646_, 3);
lean_inc_ref(v_hypotheses_5647_);
lean_dec(v___x_5646_);
v___x_5648_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode(v___x_5645_, v_hypotheses_5647_, v_eprSymBreak_5644_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_);
if (lean_obj_tag(v___x_5648_) == 0)
{
lean_object* v_a_5649_; lean_object* v___x_5651_; uint8_t v_isShared_5652_; uint8_t v_isSharedCheck_5714_; 
v_a_5649_ = lean_ctor_get(v___x_5648_, 0);
v_isSharedCheck_5714_ = !lean_is_exclusive(v___x_5648_);
if (v_isSharedCheck_5714_ == 0)
{
v___x_5651_ = v___x_5648_;
v_isShared_5652_ = v_isSharedCheck_5714_;
goto v_resetjp_5650_;
}
else
{
lean_inc(v_a_5649_);
lean_dec(v___x_5648_);
v___x_5651_ = lean_box(0);
v_isShared_5652_ = v_isSharedCheck_5714_;
goto v_resetjp_5650_;
}
v_resetjp_5650_:
{
if (lean_obj_tag(v_a_5649_) == 1)
{
lean_object* v_val_5653_; lean_object* v_fst_5654_; lean_object* v_snd_5655_; lean_object* v___x_5656_; lean_object* v_caches_5657_; lean_object* v_typeAnalysis_5658_; lean_object* v_target_5659_; uint8_t v_didChange_5660_; lean_object* v___x_5662_; uint8_t v_isShared_5663_; uint8_t v_isSharedCheck_5706_; 
v_val_5653_ = lean_ctor_get(v_a_5649_, 0);
lean_inc(v_val_5653_);
lean_dec_ref_known(v_a_5649_, 1);
v_fst_5654_ = lean_ctor_get(v_val_5653_, 0);
lean_inc(v_fst_5654_);
v_snd_5655_ = lean_ctor_get(v_val_5653_, 1);
lean_inc(v_snd_5655_);
lean_dec(v_val_5653_);
v___x_5656_ = lean_st_ref_take(v___y_5630_);
v_caches_5657_ = lean_ctor_get(v___x_5656_, 0);
v_typeAnalysis_5658_ = lean_ctor_get(v___x_5656_, 1);
v_target_5659_ = lean_ctor_get(v___x_5656_, 2);
v_didChange_5660_ = lean_ctor_get_uint8(v___x_5656_, sizeof(void*)*5);
v_isSharedCheck_5706_ = !lean_is_exclusive(v___x_5656_);
if (v_isSharedCheck_5706_ == 0)
{
lean_object* v_unused_5707_; lean_object* v_unused_5708_; 
v_unused_5707_ = lean_ctor_get(v___x_5656_, 4);
lean_dec(v_unused_5707_);
v_unused_5708_ = lean_ctor_get(v___x_5656_, 3);
lean_dec(v_unused_5708_);
v___x_5662_ = v___x_5656_;
v_isShared_5663_ = v_isSharedCheck_5706_;
goto v_resetjp_5661_;
}
else
{
lean_inc(v_target_5659_);
lean_inc(v_typeAnalysis_5658_);
lean_inc(v_caches_5657_);
lean_dec(v___x_5656_);
v___x_5662_ = lean_box(0);
v_isShared_5663_ = v_isSharedCheck_5706_;
goto v_resetjp_5661_;
}
v_resetjp_5661_:
{
lean_object* v___x_5665_; 
lean_inc(v_snd_5655_);
if (v_isShared_5663_ == 0)
{
lean_ctor_set(v___x_5662_, 4, v_snd_5655_);
lean_ctor_set(v___x_5662_, 3, v_fst_5654_);
v___x_5665_ = v___x_5662_;
goto v_reusejp_5664_;
}
else
{
lean_object* v_reuseFailAlloc_5705_; 
v_reuseFailAlloc_5705_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_5705_, 0, v_caches_5657_);
lean_ctor_set(v_reuseFailAlloc_5705_, 1, v_typeAnalysis_5658_);
lean_ctor_set(v_reuseFailAlloc_5705_, 2, v_target_5659_);
lean_ctor_set(v_reuseFailAlloc_5705_, 3, v_fst_5654_);
lean_ctor_set(v_reuseFailAlloc_5705_, 4, v_snd_5655_);
lean_ctor_set_uint8(v_reuseFailAlloc_5705_, sizeof(void*)*5, v_didChange_5660_);
v___x_5665_ = v_reuseFailAlloc_5705_;
goto v_reusejp_5664_;
}
v_reusejp_5664_:
{
lean_object* v___x_5666_; lean_object* v_groundFacts_5667_; lean_object* v___x_5690_; lean_object* v___x_5691_; uint8_t v___x_5692_; 
v___x_5666_ = lean_st_ref_put(v___y_5630_, v___x_5665_);
v_groundFacts_5667_ = lean_ctor_get(v_snd_5655_, 3);
lean_inc_ref(v_groundFacts_5667_);
lean_dec(v_snd_5655_);
v___x_5690_ = lean_unsigned_to_nat(0u);
v___x_5691_ = lean_array_get_size(v_groundFacts_5667_);
v___x_5692_ = lean_nat_dec_lt(v___x_5690_, v___x_5691_);
if (v___x_5692_ == 0)
{
goto v___jp_5668_;
}
else
{
lean_object* v___x_5693_; size_t v___x_5694_; size_t v___x_5695_; lean_object* v___x_5696_; 
v___x_5693_ = lean_box(0);
v___x_5694_ = ((size_t)0ULL);
v___x_5695_ = lean_usize_of_nat(v___x_5691_);
v___x_5696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1(v_groundFacts_5667_, v___x_5694_, v___x_5695_, v___x_5693_, v___y_5629_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_);
if (lean_obj_tag(v___x_5696_) == 0)
{
lean_dec_ref_known(v___x_5696_, 1);
goto v___jp_5668_;
}
else
{
lean_object* v_a_5697_; lean_object* v___x_5699_; uint8_t v_isShared_5700_; uint8_t v_isSharedCheck_5704_; 
lean_dec_ref(v_groundFacts_5667_);
lean_del_object(v___x_5651_);
v_a_5697_ = lean_ctor_get(v___x_5696_, 0);
v_isSharedCheck_5704_ = !lean_is_exclusive(v___x_5696_);
if (v_isSharedCheck_5704_ == 0)
{
v___x_5699_ = v___x_5696_;
v_isShared_5700_ = v_isSharedCheck_5704_;
goto v_resetjp_5698_;
}
else
{
lean_inc(v_a_5697_);
lean_dec(v___x_5696_);
v___x_5699_ = lean_box(0);
v_isShared_5700_ = v_isSharedCheck_5704_;
goto v_resetjp_5698_;
}
v_resetjp_5698_:
{
lean_object* v___x_5702_; 
if (v_isShared_5700_ == 0)
{
v___x_5702_ = v___x_5699_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_a_5697_);
v___x_5702_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
return v___x_5702_;
}
}
}
}
v___jp_5668_:
{
lean_object* v___x_5669_; lean_object* v_caches_5670_; lean_object* v_typeAnalysis_5671_; lean_object* v_target_5672_; lean_object* v_hypotheses_5673_; uint8_t v_didChange_5674_; lean_object* v_eprBvProblem_5675_; lean_object* v___x_5677_; uint8_t v_isShared_5678_; uint8_t v_isSharedCheck_5689_; 
v___x_5669_ = lean_st_ref_take(v___y_5630_);
v_caches_5670_ = lean_ctor_get(v___x_5669_, 0);
v_typeAnalysis_5671_ = lean_ctor_get(v___x_5669_, 1);
v_target_5672_ = lean_ctor_get(v___x_5669_, 2);
v_hypotheses_5673_ = lean_ctor_get(v___x_5669_, 3);
v_didChange_5674_ = lean_ctor_get_uint8(v___x_5669_, sizeof(void*)*5);
v_eprBvProblem_5675_ = lean_ctor_get(v___x_5669_, 4);
v_isSharedCheck_5689_ = !lean_is_exclusive(v___x_5669_);
if (v_isSharedCheck_5689_ == 0)
{
v___x_5677_ = v___x_5669_;
v_isShared_5678_ = v_isSharedCheck_5689_;
goto v_resetjp_5676_;
}
else
{
lean_inc(v_eprBvProblem_5675_);
lean_inc(v_hypotheses_5673_);
lean_inc(v_target_5672_);
lean_inc(v_typeAnalysis_5671_);
lean_inc(v_caches_5670_);
lean_dec(v___x_5669_);
v___x_5677_ = lean_box(0);
v_isShared_5678_ = v_isSharedCheck_5689_;
goto v_resetjp_5676_;
}
v_resetjp_5676_:
{
lean_object* v___x_5679_; lean_object* v___x_5681_; 
v___x_5679_ = l_Array_append___redArg(v_hypotheses_5673_, v_groundFacts_5667_);
lean_dec_ref(v_groundFacts_5667_);
if (v_isShared_5678_ == 0)
{
lean_ctor_set(v___x_5677_, 3, v___x_5679_);
v___x_5681_ = v___x_5677_;
goto v_reusejp_5680_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v_caches_5670_);
lean_ctor_set(v_reuseFailAlloc_5688_, 1, v_typeAnalysis_5671_);
lean_ctor_set(v_reuseFailAlloc_5688_, 2, v_target_5672_);
lean_ctor_set(v_reuseFailAlloc_5688_, 3, v___x_5679_);
lean_ctor_set(v_reuseFailAlloc_5688_, 4, v_eprBvProblem_5675_);
lean_ctor_set_uint8(v_reuseFailAlloc_5688_, sizeof(void*)*5, v_didChange_5674_);
v___x_5681_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5680_;
}
v_reusejp_5680_:
{
lean_object* v___x_5682_; uint8_t v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5686_; 
v___x_5682_ = lean_st_ref_put(v___y_5630_, v___x_5681_);
v___x_5683_ = 0;
v___x_5684_ = lean_box(v___x_5683_);
if (v_isShared_5652_ == 0)
{
lean_ctor_set(v___x_5651_, 0, v___x_5684_);
v___x_5686_ = v___x_5651_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v___x_5684_);
v___x_5686_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
return v___x_5686_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5712_; 
lean_dec(v_a_5649_);
v___x_5709_ = 0;
v___x_5710_ = lean_box(v___x_5709_);
if (v_isShared_5652_ == 0)
{
lean_ctor_set(v___x_5651_, 0, v___x_5710_);
v___x_5712_ = v___x_5651_;
goto v_reusejp_5711_;
}
else
{
lean_object* v_reuseFailAlloc_5713_; 
v_reuseFailAlloc_5713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5713_, 0, v___x_5710_);
v___x_5712_ = v_reuseFailAlloc_5713_;
goto v_reusejp_5711_;
}
v_reusejp_5711_:
{
return v___x_5712_;
}
}
}
}
else
{
lean_object* v_a_5715_; lean_object* v___x_5717_; uint8_t v_isShared_5718_; uint8_t v_isSharedCheck_5722_; 
v_a_5715_ = lean_ctor_get(v___x_5648_, 0);
v_isSharedCheck_5722_ = !lean_is_exclusive(v___x_5648_);
if (v_isSharedCheck_5722_ == 0)
{
v___x_5717_ = v___x_5648_;
v_isShared_5718_ = v_isSharedCheck_5722_;
goto v_resetjp_5716_;
}
else
{
lean_inc(v_a_5715_);
lean_dec(v___x_5648_);
v___x_5717_ = lean_box(0);
v_isShared_5718_ = v_isSharedCheck_5722_;
goto v_resetjp_5716_;
}
v_resetjp_5716_:
{
lean_object* v___x_5720_; 
if (v_isShared_5718_ == 0)
{
v___x_5720_ = v___x_5717_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5721_; 
v_reuseFailAlloc_5721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5721_, 0, v_a_5715_);
v___x_5720_ = v_reuseFailAlloc_5721_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
return v___x_5720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___lam__0___boxed(lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_){
_start:
{
lean_object* v_res_5735_; 
v_res_5735_ = l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___lam__0(v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_);
lean_dec(v___y_5733_);
lean_dec_ref(v___y_5732_);
lean_dec(v___y_5731_);
lean_dec_ref(v___y_5730_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5728_);
lean_dec(v___y_5727_);
lean_dec_ref(v___y_5726_);
lean_dec(v___y_5725_);
lean_dec(v___y_5724_);
lean_dec_ref(v___y_5723_);
return v_res_5735_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0(lean_object* v_cls_5744_, lean_object* v_msg_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_){
_start:
{
lean_object* v___x_5758_; 
v___x_5758_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___redArg(v_cls_5744_, v_msg_5745_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_);
return v___x_5758_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___boxed(lean_object* v_cls_5759_, lean_object* v_msg_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_){
_start:
{
lean_object* v_res_5773_; 
v_res_5773_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0(v_cls_5759_, v_msg_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_);
lean_dec(v___y_5771_);
lean_dec_ref(v___y_5770_);
lean_dec(v___y_5769_);
lean_dec_ref(v___y_5768_);
lean_dec(v___y_5767_);
lean_dec_ref(v___y_5766_);
lean_dec(v___y_5765_);
lean_dec_ref(v___y_5764_);
lean_dec(v___y_5763_);
lean_dec(v___y_5762_);
lean_dec_ref(v___y_5761_);
return v_res_5773_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_BitVec(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_SortInference(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_Pass(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_SortInference(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default = _init_l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default);
l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate = _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate();
lean_mark_persistent(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_EPR_Pass(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_EPR_BitVec(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_EPR_SortInference(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_EPR_Pass(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_EPR_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_EPR_SortInference(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_EPR_Pass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_EPR_Pass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_EPR_Pass(builtin);
}
#ifdef __cplusplus
}
#endif
