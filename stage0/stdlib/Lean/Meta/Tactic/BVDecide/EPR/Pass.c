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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
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
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5_spec__6(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_26_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
lean_ctor_set(v___x_26_, 2, v___x_24_);
lean_ctor_set(v___x_26_, 3, v___x_25_);
lean_ctor_set(v___x_26_, 4, v___x_25_);
lean_ctor_set(v___x_26_, 5, v___x_25_);
lean_ctor_set(v___x_26_, 6, v___x_23_);
lean_ctor_set(v___x_26_, 7, v___x_23_);
lean_ctor_set(v___x_26_, 8, v___x_23_);
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
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_432_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_432_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_432_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_432_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v_sorts_405_; lean_object* v_sortIds_406_; lean_object* v_nextSortId_407_; lean_object* v_elements_408_; lean_object* v_preds_409_; lean_object* v_usedElements_410_; lean_object* v_groundFacts_411_; lean_object* v_quantifiedFacts_412_; lean_object* v_remainingHyps_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_431_; 
v___x_404_ = lean_st_ref_take(v_a_391_);
v_sorts_405_ = lean_ctor_get(v___x_404_, 0);
v_sortIds_406_ = lean_ctor_get(v___x_404_, 1);
v_nextSortId_407_ = lean_ctor_get(v___x_404_, 2);
v_elements_408_ = lean_ctor_get(v___x_404_, 3);
v_preds_409_ = lean_ctor_get(v___x_404_, 4);
v_usedElements_410_ = lean_ctor_get(v___x_404_, 5);
v_groundFacts_411_ = lean_ctor_get(v___x_404_, 6);
v_quantifiedFacts_412_ = lean_ctor_get(v___x_404_, 7);
v_remainingHyps_413_ = lean_ctor_get(v___x_404_, 8);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_431_ == 0)
{
v___x_415_ = v___x_404_;
v_isShared_416_ = v_isSharedCheck_431_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_remainingHyps_413_);
lean_inc(v_quantifiedFacts_412_);
lean_inc(v_groundFacts_411_);
lean_inc(v_usedElements_410_);
lean_inc(v_preds_409_);
lean_inc(v_elements_408_);
lean_inc(v_nextSortId_407_);
lean_inc(v_sortIds_406_);
lean_inc(v_sorts_405_);
lean_dec(v___x_404_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_431_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_417_ = lean_box(0);
v___x_418_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__3));
lean_inc(v_a_400_);
v___x_419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_419_, 0, v_a_400_);
lean_ctor_set(v___x_419_, 1, v_level_390_);
lean_ctor_set(v___x_419_, 2, v___x_418_);
lean_inc_n(v_nextSortId_407_, 2);
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0___redArg(v_sorts_405_, v_nextSortId_407_, v___x_419_);
v___x_421_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1___redArg(v_sortIds_406_, v_a_400_, v_nextSortId_407_);
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_add(v_nextSortId_407_, v___x_422_);
lean_dec(v_nextSortId_407_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 2, v___x_423_);
lean_ctor_set(v___x_415_, 1, v___x_421_);
lean_ctor_set(v___x_415_, 0, v___x_420_);
v___x_425_ = v___x_415_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_430_, 3, v_elements_408_);
lean_ctor_set(v_reuseFailAlloc_430_, 4, v_preds_409_);
lean_ctor_set(v_reuseFailAlloc_430_, 5, v_usedElements_410_);
lean_ctor_set(v_reuseFailAlloc_430_, 6, v_groundFacts_411_);
lean_ctor_set(v_reuseFailAlloc_430_, 7, v_quantifiedFacts_412_);
lean_ctor_set(v_reuseFailAlloc_430_, 8, v_remainingHyps_413_);
v___x_425_ = v_reuseFailAlloc_430_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = lean_st_ref_put(v_a_391_, v___x_425_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_417_);
v___x_428_ = v___x_402_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_417_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec(v_level_390_);
v_a_433_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_399_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_399_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort___boxed(lean_object* v_type_441_, lean_object* v_level_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort(v_type_441_, v_level_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0(lean_object* v_00_u03b2_452_, lean_object* v_m_453_, lean_object* v_a_454_, lean_object* v_b_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0___redArg(v_m_453_, v_a_454_, v_b_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1(lean_object* v_00_u03b2_457_, lean_object* v_m_458_, lean_object* v_a_459_, lean_object* v_b_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1___redArg(v_m_458_, v_a_459_, v_b_460_);
return v___x_461_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0(lean_object* v_00_u03b2_462_, lean_object* v_a_463_, lean_object* v_x_464_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___redArg(v_a_463_, v_x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___boxed(lean_object* v_00_u03b2_466_, lean_object* v_a_467_, lean_object* v_x_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0(v_00_u03b2_466_, v_a_467_, v_x_468_);
lean_dec(v_x_468_);
lean_dec(v_a_467_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1(lean_object* v_00_u03b2_471_, lean_object* v_data_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1___redArg(v_data_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__2(lean_object* v_00_u03b2_474_, lean_object* v_a_475_, lean_object* v_b_476_, lean_object* v_x_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__2___redArg(v_a_475_, v_b_476_, v_x_477_);
return v___x_478_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4(lean_object* v_00_u03b2_479_, lean_object* v_a_480_, lean_object* v_x_481_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4___redArg(v_a_480_, v_x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4___boxed(lean_object* v_00_u03b2_483_, lean_object* v_a_484_, lean_object* v_x_485_){
_start:
{
uint8_t v_res_486_; lean_object* v_r_487_; 
v_res_486_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4(v_00_u03b2_483_, v_a_484_, v_x_485_);
lean_dec(v_x_485_);
lean_dec_ref(v_a_484_);
v_r_487_ = lean_box(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5(lean_object* v_00_u03b2_488_, lean_object* v_data_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5___redArg(v_data_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__6(lean_object* v_00_u03b2_491_, lean_object* v_a_492_, lean_object* v_b_493_, lean_object* v_x_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__6___redArg(v_a_492_, v_b_493_, v_x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_496_, lean_object* v_i_497_, lean_object* v_source_498_, lean_object* v_target_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2___redArg(v_i_497_, v_source_498_, v_target_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7(lean_object* v_00_u03b2_501_, lean_object* v_i_502_, lean_object* v_source_503_, lean_object* v_target_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7___redArg(v_i_502_, v_source_503_, v_target_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_506_, lean_object* v_x_507_, lean_object* v_x_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__1_spec__2_spec__4___redArg(v_x_507_, v_x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_510_, lean_object* v_x_511_, lean_object* v_x_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5_spec__7_spec__9___redArg(v_x_511_, v_x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement_spec__0_spec__0(lean_object* v_elem_514_, lean_object* v_a_515_, lean_object* v_x_516_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_dec(v_a_515_);
lean_dec_ref(v_elem_514_);
return v_x_516_;
}
else
{
lean_object* v_key_517_; lean_object* v_value_518_; lean_object* v_tail_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_542_; 
v_key_517_ = lean_ctor_get(v_x_516_, 0);
v_value_518_ = lean_ctor_get(v_x_516_, 1);
v_tail_519_ = lean_ctor_get(v_x_516_, 2);
v_isSharedCheck_542_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_542_ == 0)
{
v___x_521_ = v_x_516_;
v_isShared_522_ = v_isSharedCheck_542_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_tail_519_);
lean_inc(v_value_518_);
lean_inc(v_key_517_);
lean_dec(v_x_516_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_542_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
uint8_t v___x_523_; 
v___x_523_ = lean_nat_dec_eq(v_key_517_, v_a_515_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement_spec__0_spec__0(v_elem_514_, v_a_515_, v_tail_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 2, v___x_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_key_517_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_value_518_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
else
{
lean_object* v_type_528_; lean_object* v_level_529_; lean_object* v_elements_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_541_; 
lean_dec(v_key_517_);
v_type_528_ = lean_ctor_get(v_value_518_, 0);
v_level_529_ = lean_ctor_get(v_value_518_, 1);
v_elements_530_ = lean_ctor_get(v_value_518_, 2);
v_isSharedCheck_541_ = !lean_is_exclusive(v_value_518_);
if (v_isSharedCheck_541_ == 0)
{
v___x_532_ = v_value_518_;
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_elements_530_);
lean_inc(v_level_529_);
lean_inc(v_type_528_);
lean_dec(v_value_518_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_array_push(v_elements_530_, v_elem_514_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 2, v___x_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_type_528_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_level_529_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v___x_534_);
v___x_536_ = v_reuseFailAlloc_540_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v___x_536_);
lean_ctor_set(v___x_521_, 0, v_a_515_);
v___x_538_ = v___x_521_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_515_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_tail_519_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement_spec__0(lean_object* v_elem_543_, lean_object* v_m_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_size_546_; lean_object* v_buckets_547_; lean_object* v___x_548_; uint64_t v___x_549_; uint64_t v___x_550_; uint64_t v___x_551_; uint64_t v_fold_552_; uint64_t v___x_553_; uint64_t v___x_554_; uint64_t v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; size_t v___x_560_; lean_object* v_bucket_561_; uint8_t v___x_562_; 
v_size_546_ = lean_ctor_get(v_m_544_, 0);
v_buckets_547_ = lean_ctor_get(v_m_544_, 1);
v___x_548_ = lean_array_get_size(v_buckets_547_);
v___x_549_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_a_545_);
v___x_550_ = 32ULL;
v___x_551_ = lean_uint64_shift_right(v___x_549_, v___x_550_);
v_fold_552_ = lean_uint64_xor(v___x_549_, v___x_551_);
v___x_553_ = 16ULL;
v___x_554_ = lean_uint64_shift_right(v_fold_552_, v___x_553_);
v___x_555_ = lean_uint64_xor(v_fold_552_, v___x_554_);
v___x_556_ = lean_uint64_to_usize(v___x_555_);
v___x_557_ = lean_usize_of_nat(v___x_548_);
v___x_558_ = ((size_t)1ULL);
v___x_559_ = lean_usize_sub(v___x_557_, v___x_558_);
v___x_560_ = lean_usize_land(v___x_556_, v___x_559_);
v_bucket_561_ = lean_array_uget_borrowed(v_buckets_547_, v___x_560_);
v___x_562_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___redArg(v_a_545_, v_bucket_561_);
if (v___x_562_ == 0)
{
lean_dec(v_a_545_);
lean_dec_ref(v_elem_543_);
return v_m_544_;
}
else
{
lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_573_; 
lean_inc(v_bucket_561_);
lean_inc_ref(v_buckets_547_);
lean_inc(v_size_546_);
v_isSharedCheck_573_ = !lean_is_exclusive(v_m_544_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; lean_object* v_unused_575_; 
v_unused_574_ = lean_ctor_get(v_m_544_, 1);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_m_544_, 0);
lean_dec(v_unused_575_);
v___x_564_ = v_m_544_;
v_isShared_565_ = v_isSharedCheck_573_;
goto v_resetjp_563_;
}
else
{
lean_dec(v_m_544_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_573_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v_buckets_567_; lean_object* v_bucket_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_566_ = lean_box(0);
v_buckets_567_ = lean_array_uset(v_buckets_547_, v___x_560_, v___x_566_);
v_bucket_568_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement_spec__0_spec__0(v_elem_543_, v_a_545_, v_bucket_561_);
v___x_569_ = lean_array_uset(v_buckets_567_, v___x_560_, v_bucket_568_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v___x_569_);
v___x_571_ = v___x_564_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_size_546_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg(lean_object* v_elem_576_, lean_object* v_sort_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_580_; lean_object* v_sorts_581_; lean_object* v_sortIds_582_; lean_object* v_nextSortId_583_; lean_object* v_elements_584_; lean_object* v_preds_585_; lean_object* v_usedElements_586_; lean_object* v_groundFacts_587_; lean_object* v_quantifiedFacts_588_; lean_object* v_remainingHyps_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_601_; 
v___x_580_ = lean_st_ref_take(v_a_578_);
v_sorts_581_ = lean_ctor_get(v___x_580_, 0);
v_sortIds_582_ = lean_ctor_get(v___x_580_, 1);
v_nextSortId_583_ = lean_ctor_get(v___x_580_, 2);
v_elements_584_ = lean_ctor_get(v___x_580_, 3);
v_preds_585_ = lean_ctor_get(v___x_580_, 4);
v_usedElements_586_ = lean_ctor_get(v___x_580_, 5);
v_groundFacts_587_ = lean_ctor_get(v___x_580_, 6);
v_quantifiedFacts_588_ = lean_ctor_get(v___x_580_, 7);
v_remainingHyps_589_ = lean_ctor_get(v___x_580_, 8);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_601_ == 0)
{
v___x_591_ = v___x_580_;
v_isShared_592_ = v_isSharedCheck_601_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_remainingHyps_589_);
lean_inc(v_quantifiedFacts_588_);
lean_inc(v_groundFacts_587_);
lean_inc(v_usedElements_586_);
lean_inc(v_preds_585_);
lean_inc(v_elements_584_);
lean_inc(v_nextSortId_583_);
lean_inc(v_sortIds_582_);
lean_inc(v_sorts_581_);
lean_dec(v___x_580_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_601_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_593_ = lean_box(0);
lean_inc(v_sort_577_);
lean_inc_ref(v_elem_576_);
v___x_594_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement_spec__0(v_elem_576_, v_sorts_581_, v_sort_577_);
v___x_595_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1___redArg(v_elements_584_, v_elem_576_, v_sort_577_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 3, v___x_595_);
lean_ctor_set(v___x_591_, 0, v___x_594_);
v___x_597_ = v___x_591_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_sortIds_582_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_nextSortId_583_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_600_, 4, v_preds_585_);
lean_ctor_set(v_reuseFailAlloc_600_, 5, v_usedElements_586_);
lean_ctor_set(v_reuseFailAlloc_600_, 6, v_groundFacts_587_);
lean_ctor_set(v_reuseFailAlloc_600_, 7, v_quantifiedFacts_588_);
lean_ctor_set(v_reuseFailAlloc_600_, 8, v_remainingHyps_589_);
v___x_597_ = v_reuseFailAlloc_600_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_st_ref_put(v_a_578_, v___x_597_);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_593_);
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg___boxed(lean_object* v_elem_602_, lean_object* v_sort_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg(v_elem_602_, v_sort_603_, v_a_604_);
lean_dec(v_a_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement(lean_object* v_elem_607_, lean_object* v_sort_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg(v_elem_607_, v_sort_608_, v_a_609_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___boxed(lean_object* v_elem_618_, lean_object* v_sort_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement(v_elem_618_, v_sort_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerPred(lean_object* v_pred_629_, lean_object* v_argumentSorts_630_, uint8_t v_encoding_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Meta_Sym_shareCommonInc(v_pred_629_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_669_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_669_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_669_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_669_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v_sorts_646_; lean_object* v_sortIds_647_; lean_object* v_nextSortId_648_; lean_object* v_elements_649_; lean_object* v_preds_650_; lean_object* v_usedElements_651_; lean_object* v_groundFacts_652_; lean_object* v_quantifiedFacts_653_; lean_object* v_remainingHyps_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_668_; 
v___x_645_ = lean_st_ref_take(v_a_632_);
v_sorts_646_ = lean_ctor_get(v___x_645_, 0);
v_sortIds_647_ = lean_ctor_get(v___x_645_, 1);
v_nextSortId_648_ = lean_ctor_get(v___x_645_, 2);
v_elements_649_ = lean_ctor_get(v___x_645_, 3);
v_preds_650_ = lean_ctor_get(v___x_645_, 4);
v_usedElements_651_ = lean_ctor_get(v___x_645_, 5);
v_groundFacts_652_ = lean_ctor_get(v___x_645_, 6);
v_quantifiedFacts_653_ = lean_ctor_get(v___x_645_, 7);
v_remainingHyps_654_ = lean_ctor_get(v___x_645_, 8);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_668_ == 0)
{
v___x_656_ = v___x_645_;
v_isShared_657_ = v_isSharedCheck_668_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_remainingHyps_654_);
lean_inc(v_quantifiedFacts_653_);
lean_inc(v_groundFacts_652_);
lean_inc(v_usedElements_651_);
lean_inc(v_preds_650_);
lean_inc(v_elements_649_);
lean_inc(v_nextSortId_648_);
lean_inc(v_sortIds_647_);
lean_inc(v_sorts_646_);
lean_dec(v___x_645_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_668_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_658_ = lean_box(0);
v___x_659_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_659_, 0, v_argumentSorts_630_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*1, v_encoding_631_);
v___x_660_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1___redArg(v_preds_650_, v_a_641_, v___x_659_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v___x_660_);
v___x_662_ = v___x_656_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_sorts_646_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_sortIds_647_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_nextSortId_648_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v_elements_649_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_667_, 5, v_usedElements_651_);
lean_ctor_set(v_reuseFailAlloc_667_, 6, v_groundFacts_652_);
lean_ctor_set(v_reuseFailAlloc_667_, 7, v_quantifiedFacts_653_);
lean_ctor_set(v_reuseFailAlloc_667_, 8, v_remainingHyps_654_);
v___x_662_ = v_reuseFailAlloc_667_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_663_ = lean_st_ref_put(v_a_632_, v___x_662_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_658_);
v___x_665_ = v___x_643_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_658_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_argumentSorts_630_);
v_a_670_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_640_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_640_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerPred___boxed(lean_object* v_pred_678_, lean_object* v_argumentSorts_679_, lean_object* v_encoding_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
uint8_t v_encoding_boxed_689_; lean_object* v_res_690_; 
v_encoding_boxed_689_ = lean_unbox(v_encoding_680_);
v_res_690_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerPred(v_pred_678_, v_argumentSorts_679_, v_encoding_boxed_689_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___redArg(lean_object* v_a_691_, lean_object* v_x_692_){
_start:
{
if (lean_obj_tag(v_x_692_) == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_box(0);
return v___x_693_;
}
else
{
lean_object* v_key_694_; lean_object* v_value_695_; lean_object* v_tail_696_; size_t v___x_697_; size_t v___x_698_; uint8_t v___x_699_; 
v_key_694_ = lean_ctor_get(v_x_692_, 0);
v_value_695_ = lean_ctor_get(v_x_692_, 1);
v_tail_696_ = lean_ctor_get(v_x_692_, 2);
v___x_697_ = lean_ptr_addr(v_key_694_);
v___x_698_ = lean_ptr_addr(v_a_691_);
v___x_699_ = lean_usize_dec_eq(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
v_x_692_ = v_tail_696_;
goto _start;
}
else
{
lean_object* v___x_701_; 
lean_inc(v_value_695_);
v___x_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_701_, 0, v_value_695_);
return v___x_701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_702_, lean_object* v_x_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___redArg(v_a_702_, v_x_703_);
lean_dec(v_x_703_);
lean_dec_ref(v_a_702_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(lean_object* v_m_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_buckets_707_; lean_object* v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; uint64_t v___x_712_; uint64_t v___x_713_; uint64_t v___x_714_; uint64_t v_fold_715_; uint64_t v___x_716_; uint64_t v___x_717_; uint64_t v___x_718_; size_t v___x_719_; size_t v___x_720_; size_t v___x_721_; size_t v___x_722_; size_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_buckets_707_ = lean_ctor_get(v_m_705_, 1);
v___x_708_ = lean_array_get_size(v_buckets_707_);
v___x_709_ = lean_ptr_addr(v_a_706_);
v___x_710_ = ((size_t)3ULL);
v___x_711_ = lean_usize_shift_right(v___x_709_, v___x_710_);
v___x_712_ = lean_usize_to_uint64(v___x_711_);
v___x_713_ = 32ULL;
v___x_714_ = lean_uint64_shift_right(v___x_712_, v___x_713_);
v_fold_715_ = lean_uint64_xor(v___x_712_, v___x_714_);
v___x_716_ = 16ULL;
v___x_717_ = lean_uint64_shift_right(v_fold_715_, v___x_716_);
v___x_718_ = lean_uint64_xor(v_fold_715_, v___x_717_);
v___x_719_ = lean_uint64_to_usize(v___x_718_);
v___x_720_ = lean_usize_of_nat(v___x_708_);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_sub(v___x_720_, v___x_721_);
v___x_723_ = lean_usize_land(v___x_719_, v___x_722_);
v___x_724_ = lean_array_uget_borrowed(v_buckets_707_, v___x_723_);
v___x_725_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___redArg(v_a_706_, v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg___boxed(lean_object* v_m_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_m_726_, v_a_727_);
lean_dec_ref(v_a_727_);
lean_dec_ref(v_m_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg(lean_object* v_type_730_, lean_object* v_acc_731_, lean_object* v_a_732_){
_start:
{
switch(lean_obj_tag(v_type_730_))
{
case 3:
{
lean_object* v_u_737_; 
v_u_737_ = lean_ctor_get(v_type_730_, 0);
if (lean_obj_tag(v_u_737_) == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_738_ = lean_array_get_size(v_acc_731_);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_nat_dec_eq(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
uint8_t v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_741_ = 0;
v___x_742_ = lean_box(v___x_741_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v_acc_731_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec_ref(v_acc_731_);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
else
{
lean_dec_ref(v_acc_731_);
goto v___jp_734_;
}
}
case 4:
{
lean_object* v_declName_748_; 
v_declName_748_ = lean_ctor_get(v_type_730_, 0);
if (lean_obj_tag(v_declName_748_) == 1)
{
lean_object* v_pre_749_; 
v_pre_749_ = lean_ctor_get(v_declName_748_, 0);
if (lean_obj_tag(v_pre_749_) == 0)
{
lean_object* v_us_750_; lean_object* v_str_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v_us_750_ = lean_ctor_get(v_type_730_, 1);
v_str_751_ = lean_ctor_get(v_declName_748_, 1);
v___x_752_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___closed__0));
v___x_753_ = lean_string_dec_eq(v_str_751_, v___x_752_);
if (v___x_753_ == 0)
{
lean_dec_ref(v_acc_731_);
goto v___jp_734_;
}
else
{
if (lean_obj_tag(v_us_750_) == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_754_ = lean_array_get_size(v_acc_731_);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_nat_dec_eq(v___x_754_, v___x_755_);
if (v___x_756_ == 0)
{
uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_757_ = 1;
v___x_758_ = lean_box(v___x_757_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_acc_731_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; 
lean_dec_ref(v_acc_731_);
v___x_762_ = lean_box(0);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
}
else
{
lean_dec_ref(v_acc_731_);
goto v___jp_734_;
}
}
}
else
{
lean_dec_ref(v_acc_731_);
goto v___jp_734_;
}
}
else
{
lean_dec_ref(v_acc_731_);
goto v___jp_734_;
}
}
case 7:
{
lean_object* v_binderType_764_; lean_object* v_body_765_; uint8_t v___x_766_; 
v_binderType_764_ = lean_ctor_get(v_type_730_, 1);
v_body_765_ = lean_ctor_get(v_type_730_, 2);
v___x_766_ = l_Lean_Expr_hasLooseBVars(v_body_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v_sortIds_768_; lean_object* v___x_769_; 
v___x_767_ = lean_st_ref_get(v_a_732_);
v_sortIds_768_ = lean_ctor_get(v___x_767_, 1);
lean_inc_ref(v_sortIds_768_);
lean_dec(v___x_767_);
v___x_769_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_sortIds_768_, v_binderType_764_);
lean_dec_ref(v_sortIds_768_);
if (lean_obj_tag(v___x_769_) == 1)
{
lean_object* v_val_770_; lean_object* v___x_771_; 
v_val_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v___x_769_, 1);
v___x_771_ = lean_array_push(v_acc_731_, v_val_770_);
v_type_730_ = v_body_765_;
v_acc_731_ = v___x_771_;
goto _start;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec(v___x_769_);
lean_dec_ref(v_acc_731_);
v___x_773_ = lean_box(0);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec_ref(v_acc_731_);
v___x_775_ = lean_box(0);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
default: 
{
lean_dec_ref(v_acc_731_);
goto v___jp_734_;
}
}
v___jp_734_:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_box(0);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg___boxed(lean_object* v_type_777_, lean_object* v_acc_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg(v_type_777_, v_acc_778_, v_a_779_);
lean_dec(v_a_779_);
lean_dec_ref(v_type_777_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go(lean_object* v_type_782_, lean_object* v_acc_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg(v_type_782_, v_acc_783_, v_a_784_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___boxed(lean_object* v_type_793_, lean_object* v_acc_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go(v_type_793_, v_acc_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_type_793_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0(lean_object* v_00_u03b2_804_, lean_object* v_m_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_m_805_, v_a_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_808_, lean_object* v_m_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0(v_00_u03b2_808_, v_m_809_, v_a_810_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_m_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0(lean_object* v_00_u03b2_812_, lean_object* v_a_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___redArg(v_a_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_816_, lean_object* v_a_817_, lean_object* v_x_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0_spec__0(v_00_u03b2_816_, v_a_817_, v_x_818_);
lean_dec(v_x_818_);
lean_dec_ref(v_a_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg(lean_object* v_type_822_, lean_object* v_a_823_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg___closed__0));
v___x_826_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go___redArg(v_type_822_, v___x_825_, v_a_823_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg___boxed(lean_object* v_type_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg(v_type_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_type_827_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f(lean_object* v_type_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg(v_type_831_, v_a_832_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___boxed(lean_object* v_type_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f(v_type_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_type_841_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processLocalDecl(lean_object* v_decl_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
uint8_t v___x_863_; 
v___x_863_ = l_Lean_LocalDecl_isImplementationDetail(v_decl_851_);
if (v___x_863_ == 0)
{
uint8_t v___x_864_; 
v___x_864_ = l_Lean_LocalDecl_isLet(v_decl_851_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = l_Lean_LocalDecl_type(v_decl_851_);
v___x_866_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_865_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
if (lean_obj_tag(v_a_867_) == 3)
{
lean_object* v_u_918_; 
v_u_918_ = lean_ctor_get(v_a_867_, 0);
if (lean_obj_tag(v_u_918_) == 1)
{
lean_object* v_a_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
lean_inc_ref(v_u_918_);
lean_dec_ref_known(v_a_867_, 1);
v_a_919_ = lean_ctor_get(v_u_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v_u_918_, 1);
v___x_920_ = l_Lean_LocalDecl_toExpr(v_decl_851_);
v___x_921_ = l_Lean_Meta_Sym_shareCommonInc(v___x_920_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_923_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_921_, 1);
v___x_923_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort(v_a_922_, v_a_919_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
return v___x_923_;
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_a_919_);
v_a_924_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_921_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_921_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
v___y_869_ = v_a_852_;
v___y_870_ = v_a_853_;
v___y_871_ = v_a_854_;
v___y_872_ = v_a_855_;
v___y_873_ = v_a_856_;
v___y_874_ = v_a_857_;
v___y_875_ = v_a_858_;
goto v___jp_868_;
}
}
else
{
v___y_869_ = v_a_852_;
v___y_870_ = v_a_853_;
v___y_871_ = v_a_854_;
v___y_872_ = v_a_855_;
v___y_873_ = v_a_856_;
v___y_874_ = v_a_857_;
v___y_875_ = v_a_858_;
goto v___jp_868_;
}
v___jp_868_:
{
lean_object* v___x_876_; lean_object* v_sortIds_877_; lean_object* v___x_878_; 
v___x_876_ = lean_st_ref_get(v___y_869_);
v_sortIds_877_ = lean_ctor_get(v___x_876_, 1);
lean_inc_ref(v_sortIds_877_);
lean_dec(v___x_876_);
v___x_878_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_sortIds_877_, v_a_867_);
lean_dec_ref(v_sortIds_877_);
if (lean_obj_tag(v___x_878_) == 1)
{
lean_object* v_val_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec(v_a_867_);
v_val_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_val_879_);
lean_dec_ref_known(v___x_878_, 1);
v___x_880_ = l_Lean_LocalDecl_toExpr(v_decl_851_);
v___x_881_ = l_Lean_Meta_Sym_shareCommonInc(v___x_880_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg(v_a_882_, v_val_879_, v___y_869_);
return v___x_883_;
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec(v_val_879_);
v_a_884_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_881_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_881_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v___x_892_; lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_917_; 
lean_dec(v___x_878_);
v___x_892_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg(v_a_867_, v___y_869_);
lean_dec(v_a_867_);
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_917_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_917_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_917_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
if (lean_obj_tag(v_a_893_) == 1)
{
lean_object* v_val_897_; lean_object* v_fst_898_; lean_object* v_snd_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_del_object(v___x_895_);
v_val_897_ = lean_ctor_get(v_a_893_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v_a_893_, 1);
v_fst_898_ = lean_ctor_get(v_val_897_, 0);
lean_inc(v_fst_898_);
v_snd_899_ = lean_ctor_get(v_val_897_, 1);
lean_inc(v_snd_899_);
lean_dec(v_val_897_);
v___x_900_ = l_Lean_LocalDecl_toExpr(v_decl_851_);
v___x_901_ = l_Lean_Meta_Sym_shareCommonInc(v___x_900_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; uint8_t v___x_903_; lean_object* v___x_904_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
v___x_903_ = lean_unbox(v_snd_899_);
lean_dec(v_snd_899_);
v___x_904_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerPred(v_a_902_, v_fst_898_, v___x_903_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
return v___x_904_;
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec(v_snd_899_);
lean_dec(v_fst_898_);
v_a_905_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_901_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_901_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_915_; 
lean_dec(v_a_893_);
lean_dec_ref(v_decl_851_);
v___x_913_ = lean_box(0);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_913_);
v___x_915_ = v___x_895_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v_decl_851_);
v_a_932_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_866_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_866_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_dec_ref(v_decl_851_);
goto v___jp_860_;
}
}
else
{
lean_dec_ref(v_decl_851_);
goto v___jp_860_;
}
v___jp_860_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_box(0);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processLocalDecl___boxed(lean_object* v_decl_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processLocalDecl(v_decl_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort___redArg(lean_object* v_a_950_){
_start:
{
lean_object* v___x_952_; lean_object* v_usedElements_953_; lean_object* v_cache_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_965_; 
v___x_952_ = lean_st_ref_take(v_a_950_);
v_usedElements_953_ = lean_ctor_get(v___x_952_, 0);
v_cache_954_ = lean_ctor_get(v___x_952_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_965_ == 0)
{
v___x_956_ = v___x_952_;
v_isShared_957_ = v_isSharedCheck_965_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_cache_954_);
lean_inc(v_usedElements_953_);
lean_dec(v___x_952_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_965_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; uint8_t v___x_959_; lean_object* v___x_961_; 
v___x_958_ = lean_box(0);
v___x_959_ = 1;
if (v_isShared_957_ == 0)
{
v___x_961_ = v___x_956_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_usedElements_953_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_cache_954_);
v___x_961_ = v_reuseFailAlloc_964_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*2, v___x_959_);
v___x_962_ = lean_st_ref_put(v_a_950_, v___x_961_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_958_);
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort___redArg___boxed(lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort___redArg(v_a_966_);
lean_dec(v_a_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort(lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v___x_979_; lean_object* v_usedElements_980_; lean_object* v_cache_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_992_; 
v___x_979_ = lean_st_ref_take(v_a_970_);
v_usedElements_980_ = lean_ctor_get(v___x_979_, 0);
v_cache_981_ = lean_ctor_get(v___x_979_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_992_ == 0)
{
v___x_983_ = v___x_979_;
v_isShared_984_ = v_isSharedCheck_992_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_cache_981_);
lean_inc(v_usedElements_980_);
lean_dec(v___x_979_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_992_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; uint8_t v___x_986_; lean_object* v___x_988_; 
v___x_985_ = lean_box(0);
v___x_986_ = 1;
if (v_isShared_984_ == 0)
{
v___x_988_ = v___x_983_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_usedElements_980_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_cache_981_);
v___x_988_ = v_reuseFailAlloc_991_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_ctor_set_uint8(v___x_988_, sizeof(void*)*2, v___x_986_);
v___x_989_ = lean_st_ref_put(v_a_970_, v___x_988_);
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_985_);
return v___x_990_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort___boxed(lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_markMentionsSort(v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm_spec__0___redArg(lean_object* v_m_1004_, lean_object* v_a_1005_, lean_object* v_b_1006_){
_start:
{
lean_object* v_size_1007_; lean_object* v_buckets_1008_; lean_object* v___x_1009_; size_t v___x_1010_; size_t v___x_1011_; size_t v___x_1012_; uint64_t v___x_1013_; uint64_t v___x_1014_; uint64_t v___x_1015_; uint64_t v_fold_1016_; uint64_t v___x_1017_; uint64_t v___x_1018_; uint64_t v___x_1019_; size_t v___x_1020_; size_t v___x_1021_; size_t v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; lean_object* v_bkt_1025_; uint8_t v___x_1026_; 
v_size_1007_ = lean_ctor_get(v_m_1004_, 0);
v_buckets_1008_ = lean_ctor_get(v_m_1004_, 1);
v___x_1009_ = lean_array_get_size(v_buckets_1008_);
v___x_1010_ = lean_ptr_addr(v_a_1005_);
v___x_1011_ = ((size_t)3ULL);
v___x_1012_ = lean_usize_shift_right(v___x_1010_, v___x_1011_);
v___x_1013_ = lean_usize_to_uint64(v___x_1012_);
v___x_1014_ = 32ULL;
v___x_1015_ = lean_uint64_shift_right(v___x_1013_, v___x_1014_);
v_fold_1016_ = lean_uint64_xor(v___x_1013_, v___x_1015_);
v___x_1017_ = 16ULL;
v___x_1018_ = lean_uint64_shift_right(v_fold_1016_, v___x_1017_);
v___x_1019_ = lean_uint64_xor(v_fold_1016_, v___x_1018_);
v___x_1020_ = lean_uint64_to_usize(v___x_1019_);
v___x_1021_ = lean_usize_of_nat(v___x_1009_);
v___x_1022_ = ((size_t)1ULL);
v___x_1023_ = lean_usize_sub(v___x_1021_, v___x_1022_);
v___x_1024_ = lean_usize_land(v___x_1020_, v___x_1023_);
v_bkt_1025_ = lean_array_uget_borrowed(v_buckets_1008_, v___x_1024_);
v___x_1026_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4___redArg(v_a_1005_, v_bkt_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1047_; 
lean_inc_ref(v_buckets_1008_);
lean_inc(v_size_1007_);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_m_1004_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; lean_object* v_unused_1049_; 
v_unused_1048_ = lean_ctor_get(v_m_1004_, 1);
lean_dec(v_unused_1048_);
v_unused_1049_ = lean_ctor_get(v_m_1004_, 0);
lean_dec(v_unused_1049_);
v___x_1028_ = v_m_1004_;
v_isShared_1029_ = v_isSharedCheck_1047_;
goto v_resetjp_1027_;
}
else
{
lean_dec(v_m_1004_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1047_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v_size_x27_1031_; lean_object* v___x_1032_; lean_object* v_buckets_x27_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1030_ = lean_unsigned_to_nat(1u);
v_size_x27_1031_ = lean_nat_add(v_size_1007_, v___x_1030_);
lean_dec(v_size_1007_);
lean_inc(v_bkt_1025_);
v___x_1032_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1032_, 0, v_a_1005_);
lean_ctor_set(v___x_1032_, 1, v_b_1006_);
lean_ctor_set(v___x_1032_, 2, v_bkt_1025_);
v_buckets_x27_1033_ = lean_array_uset(v_buckets_1008_, v___x_1024_, v___x_1032_);
v___x_1034_ = lean_unsigned_to_nat(4u);
v___x_1035_ = lean_nat_mul(v_size_x27_1031_, v___x_1034_);
v___x_1036_ = lean_unsigned_to_nat(3u);
v___x_1037_ = lean_nat_div(v___x_1035_, v___x_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_array_get_size(v_buckets_x27_1033_);
v___x_1039_ = lean_nat_dec_le(v___x_1037_, v___x_1038_);
lean_dec(v___x_1037_);
if (v___x_1039_ == 0)
{
lean_object* v_val_1040_; lean_object* v___x_1042_; 
v_val_1040_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__5___redArg(v_buckets_x27_1033_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v_val_1040_);
lean_ctor_set(v___x_1028_, 0, v_size_x27_1031_);
v___x_1042_ = v___x_1028_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_size_x27_1031_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_val_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
else
{
lean_object* v___x_1045_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v_buckets_x27_1033_);
lean_ctor_set(v___x_1028_, 0, v_size_x27_1031_);
v___x_1045_ = v___x_1028_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_size_x27_1031_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_buckets_x27_1033_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_dec(v_b_1006_);
lean_dec_ref(v_a_1005_);
return v_m_1004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(lean_object* v_e_1050_, lean_object* v_depth_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
if (lean_obj_tag(v_e_1050_) == 0)
{
lean_object* v_deBruijnIndex_1056_; uint8_t v___x_1057_; 
v_deBruijnIndex_1056_ = lean_ctor_get(v_e_1050_, 0);
lean_inc(v_deBruijnIndex_1056_);
lean_dec_ref_known(v_e_1050_, 1);
v___x_1057_ = lean_nat_dec_lt(v_deBruijnIndex_1056_, v_depth_1051_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1058_ = lean_nat_sub(v_deBruijnIndex_1056_, v_depth_1051_);
lean_dec(v_deBruijnIndex_1056_);
v___x_1059_ = lean_array_get_size(v_a_1052_);
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1061_ = lean_nat_sub(v___x_1059_, v___x_1060_);
v___x_1062_ = lean_nat_sub(v___x_1061_, v___x_1058_);
lean_dec(v___x_1058_);
lean_dec(v___x_1061_);
v___x_1063_ = lean_nat_dec_lt(v___x_1062_, v___x_1059_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec(v___x_1062_);
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = lean_array_fget_borrowed(v_a_1052_, v___x_1062_);
lean_dec(v___x_1062_);
lean_inc(v___x_1066_);
v___x_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_dec(v_deBruijnIndex_1056_);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
else
{
lean_object* v___x_1071_; lean_object* v_elements_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_st_ref_get(v_a_1054_);
v_elements_1072_ = lean_ctor_get(v___x_1071_, 3);
lean_inc_ref(v_elements_1072_);
lean_dec(v___x_1071_);
v___x_1073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_elements_1072_, v_e_1050_);
lean_dec_ref(v_elements_1072_);
if (lean_obj_tag(v___x_1073_) == 1)
{
lean_object* v___x_1074_; lean_object* v_usedElements_1075_; lean_object* v_cache_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1100_; 
v___x_1074_ = lean_st_ref_take(v_a_1053_);
v_usedElements_1075_ = lean_ctor_get(v___x_1074_, 0);
v_cache_1076_ = lean_ctor_get(v___x_1074_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1078_ = v___x_1074_;
v_isShared_1079_ = v_isSharedCheck_1100_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_cache_1076_);
lean_inc(v_usedElements_1075_);
lean_dec(v___x_1074_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1100_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
uint8_t v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = 1;
if (v_isShared_1079_ == 0)
{
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_usedElements_1075_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_cache_1076_);
v___x_1082_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v_mentionsSort_1085_; lean_object* v_usedElements_1086_; lean_object* v_cache_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1098_; 
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*2, v___x_1080_);
v___x_1083_ = lean_st_ref_put(v_a_1053_, v___x_1082_);
v___x_1084_ = lean_st_ref_take(v_a_1053_);
v_mentionsSort_1085_ = lean_ctor_get_uint8(v___x_1084_, sizeof(void*)*2);
v_usedElements_1086_ = lean_ctor_get(v___x_1084_, 0);
v_cache_1087_ = lean_ctor_get(v___x_1084_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1089_ = v___x_1084_;
v_isShared_1090_ = v_isSharedCheck_1098_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_cache_1087_);
lean_inc(v_usedElements_1086_);
lean_dec(v___x_1084_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1098_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1091_ = lean_box(0);
v___x_1092_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm_spec__0___redArg(v_usedElements_1086_, v_e_1050_, v___x_1091_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_cache_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1097_, sizeof(void*)*2, v_mentionsSort_1085_);
v___x_1094_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_st_ref_put(v_a_1053_, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1073_);
return v___x_1096_;
}
}
}
}
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec(v___x_1073_);
lean_dec_ref(v_e_1050_);
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg___boxed(lean_object* v_e_1103_, lean_object* v_depth_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(v_e_1103_, v_depth_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_depth_1104_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm(lean_object* v_e_1110_, lean_object* v_depth_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(v_e_1110_, v_depth_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___boxed(lean_object* v_e_1123_, lean_object* v_depth_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm(v_e_1123_, v_depth_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_depth_1124_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm_spec__0(lean_object* v_00_u03b2_1136_, lean_object* v_m_1137_, lean_object* v_a_1138_, lean_object* v_b_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm_spec__0___redArg(v_m_1137_, v_a_1138_, v_b_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___redArg(lean_object* v_00_u03b1_1141_, lean_object* v_lhs_1142_, lean_object* v_rhs_1143_, lean_object* v_depth_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___x_1149_; lean_object* v_sortIds_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_st_ref_get(v_a_1147_);
v_sortIds_1150_ = lean_ctor_get(v___x_1149_, 1);
lean_inc_ref(v_sortIds_1150_);
lean_dec(v___x_1149_);
v___x_1151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_sortIds_1150_, v_00_u03b1_1141_);
lean_dec_ref(v_sortIds_1150_);
if (lean_obj_tag(v___x_1151_) == 1)
{
lean_object* v_val_1152_; lean_object* v___x_1153_; lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1186_; 
v_val_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v___x_1151_, 1);
v___x_1153_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(v_lhs_1142_, v_depth_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1186_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1186_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
if (lean_obj_tag(v_a_1154_) == 1)
{
lean_object* v_val_1158_; lean_object* v___x_1159_; lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1180_; 
lean_del_object(v___x_1156_);
v_val_1158_ = lean_ctor_get(v_a_1154_, 0);
lean_inc(v_val_1158_);
lean_dec_ref_known(v_a_1154_, 1);
v___x_1159_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(v_rhs_1143_, v_depth_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1180_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1180_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
if (lean_obj_tag(v_a_1160_) == 1)
{
lean_object* v_val_1164_; uint8_t v___x_1165_; 
v_val_1164_ = lean_ctor_get(v_a_1160_, 0);
lean_inc(v_val_1164_);
lean_dec_ref_known(v_a_1160_, 1);
v___x_1165_ = lean_nat_dec_eq(v_val_1158_, v_val_1152_);
lean_dec(v_val_1158_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
lean_dec(v_val_1164_);
lean_dec(v_val_1152_);
v___x_1166_ = lean_box(v___x_1165_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1166_);
v___x_1168_ = v___x_1162_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
else
{
uint8_t v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1170_ = lean_nat_dec_eq(v_val_1164_, v_val_1152_);
lean_dec(v_val_1152_);
lean_dec(v_val_1164_);
v___x_1171_ = lean_box(v___x_1170_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1171_);
v___x_1173_ = v___x_1162_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
else
{
uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_dec(v_a_1160_);
lean_dec(v_val_1158_);
lean_dec(v_val_1152_);
v___x_1175_ = 0;
v___x_1176_ = lean_box(v___x_1175_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1176_);
v___x_1178_ = v___x_1162_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
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
else
{
uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
lean_dec(v_a_1154_);
lean_dec(v_val_1152_);
lean_dec_ref(v_rhs_1143_);
v___x_1181_ = 0;
v___x_1182_ = lean_box(v___x_1181_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v___x_1182_);
v___x_1184_ = v___x_1156_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec(v___x_1151_);
lean_dec_ref(v_rhs_1143_);
lean_dec_ref(v_lhs_1142_);
v___x_1187_ = 0;
v___x_1188_ = lean_box(v___x_1187_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___redArg___boxed(lean_object* v_00_u03b1_1190_, lean_object* v_lhs_1191_, lean_object* v_rhs_1192_, lean_object* v_depth_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___redArg(v_00_u03b1_1190_, v_lhs_1191_, v_rhs_1192_, v_depth_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
lean_dec(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_depth_1193_);
lean_dec_ref(v_00_u03b1_1190_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq(lean_object* v_00_u03b1_1199_, lean_object* v_lhs_1200_, lean_object* v_rhs_1201_, lean_object* v_depth_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___redArg(v_00_u03b1_1199_, v_lhs_1200_, v_rhs_1201_, v_depth_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___boxed(lean_object* v_00_u03b1_1214_, lean_object* v_lhs_1215_, lean_object* v_rhs_1216_, lean_object* v_depth_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq(v_00_u03b1_1214_, v_lhs_1215_, v_rhs_1216_, v_depth_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_depth_1217_);
lean_dec_ref(v_00_u03b1_1214_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg(lean_object* v_depth_1232_, lean_object* v_as_1233_, size_t v_sz_1234_, size_t v_i_1235_, lean_object* v_b_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v___x_1241_; 
v___x_1241_ = lean_usize_dec_lt(v_i_1235_, v_sz_1234_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v_b_1236_);
return v___x_1242_;
}
else
{
lean_object* v_snd_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1306_; 
v_snd_1243_ = lean_ctor_get(v_b_1236_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_b_1236_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v_b_1236_, 0);
lean_dec(v_unused_1307_);
v___x_1245_ = v_b_1236_;
v_isShared_1246_ = v_isSharedCheck_1306_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_snd_1243_);
lean_dec(v_b_1236_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1306_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v_array_1247_; lean_object* v_start_1248_; lean_object* v_stop_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_array_1247_ = lean_ctor_get(v_snd_1243_, 0);
v_start_1248_ = lean_ctor_get(v_snd_1243_, 1);
v_stop_1249_ = lean_ctor_get(v_snd_1243_, 2);
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_nat_dec_lt(v_start_1248_, v_stop_1249_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1253_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1250_);
v___x_1253_ = v___x_1245_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_snd_1243_);
v___x_1253_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
else
{
lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1302_; 
lean_inc(v_stop_1249_);
lean_inc(v_start_1248_);
lean_inc_ref(v_array_1247_);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_snd_1243_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; lean_object* v_unused_1304_; lean_object* v_unused_1305_; 
v_unused_1303_ = lean_ctor_get(v_snd_1243_, 2);
lean_dec(v_unused_1303_);
v_unused_1304_ = lean_ctor_get(v_snd_1243_, 1);
lean_dec(v_unused_1304_);
v_unused_1305_ = lean_ctor_get(v_snd_1243_, 0);
lean_dec(v_unused_1305_);
v___x_1257_ = v_snd_1243_;
v_isShared_1258_ = v_isSharedCheck_1302_;
goto v_resetjp_1256_;
}
else
{
lean_dec(v_snd_1243_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1302_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
v_a_1259_ = lean_array_uget_borrowed(v_as_1233_, v_i_1235_);
v___x_1260_ = lean_array_fget(v_array_1247_, v_start_1248_);
v___x_1261_ = lean_unsigned_to_nat(1u);
v___x_1262_ = lean_nat_add(v_start_1248_, v___x_1261_);
lean_dec(v_start_1248_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v___x_1262_);
v___x_1264_ = v___x_1257_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_array_1247_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1301_, 2, v_stop_1249_);
v___x_1264_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; 
lean_inc(v_a_1259_);
v___x_1265_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm___redArg(v_a_1259_, v_depth_1232_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1292_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1292_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1292_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
if (lean_obj_tag(v_a_1266_) == 1)
{
lean_object* v_val_1270_; uint8_t v___x_1271_; 
v_val_1270_ = lean_ctor_get(v_a_1266_, 0);
lean_inc(v_val_1270_);
lean_dec_ref_known(v_a_1266_, 1);
v___x_1271_ = lean_nat_dec_eq(v_val_1270_, v___x_1260_);
lean_dec(v___x_1260_);
lean_dec(v_val_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg___closed__0));
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1264_);
lean_ctor_set(v___x_1245_, 0, v___x_1272_);
v___x_1274_ = v___x_1245_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v___x_1264_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1276_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1274_);
v___x_1276_ = v___x_1268_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_object* v___x_1280_; 
lean_del_object(v___x_1268_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1264_);
lean_ctor_set(v___x_1245_, 0, v___x_1250_);
v___x_1280_ = v___x_1245_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1264_);
v___x_1280_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
size_t v___x_1281_; size_t v___x_1282_; 
v___x_1281_ = ((size_t)1ULL);
v___x_1282_ = lean_usize_add(v_i_1235_, v___x_1281_);
v_i_1235_ = v___x_1282_;
v_b_1236_ = v___x_1280_;
goto _start;
}
}
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
lean_dec(v_a_1266_);
lean_dec(v___x_1260_);
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg___closed__0));
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1264_);
lean_ctor_set(v___x_1245_, 0, v___x_1285_);
v___x_1287_ = v___x_1245_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1264_);
v___x_1287_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1289_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1287_);
v___x_1289_ = v___x_1268_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref(v___x_1264_);
lean_dec(v___x_1260_);
lean_del_object(v___x_1245_);
v_a_1293_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1265_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1265_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg___boxed(lean_object* v_depth_1308_, lean_object* v_as_1309_, lean_object* v_sz_1310_, lean_object* v_i_1311_, lean_object* v_b_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
size_t v_sz_boxed_1317_; size_t v_i_boxed_1318_; lean_object* v_res_1319_; 
v_sz_boxed_1317_ = lean_unbox_usize(v_sz_1310_);
lean_dec(v_sz_1310_);
v_i_boxed_1318_ = lean_unbox_usize(v_i_1311_);
lean_dec(v_i_1311_);
v_res_1319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg(v_depth_1308_, v_as_1309_, v_sz_boxed_1317_, v_i_boxed_1318_, v_b_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec_ref(v_as_1309_);
lean_dec(v_depth_1308_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__1(lean_object* v_depth_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
if (lean_obj_tag(v_x_1321_) == 5)
{
lean_object* v_fn_1334_; lean_object* v_arg_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_fn_1334_ = lean_ctor_get(v_x_1321_, 0);
lean_inc_ref(v_fn_1334_);
v_arg_1335_ = lean_ctor_get(v_x_1321_, 1);
lean_inc_ref(v_arg_1335_);
lean_dec_ref_known(v_x_1321_, 2);
v___x_1336_ = lean_array_set(v_x_1322_, v_x_1323_, v_arg_1335_);
v___x_1337_ = lean_unsigned_to_nat(1u);
v___x_1338_ = lean_nat_sub(v_x_1323_, v___x_1337_);
lean_dec(v_x_1323_);
v_x_1321_ = v_fn_1334_;
v_x_1322_ = v___x_1336_;
v_x_1323_ = v___x_1338_;
goto _start;
}
else
{
lean_object* v___x_1340_; lean_object* v_preds_1341_; lean_object* v___x_1342_; 
lean_dec(v_x_1323_);
v___x_1340_ = lean_st_ref_get(v___y_1326_);
v_preds_1341_ = lean_ctor_get(v___x_1340_, 4);
lean_inc_ref(v_preds_1341_);
lean_dec(v___x_1340_);
v___x_1342_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_preds_1341_, v_x_1321_);
lean_dec_ref(v_x_1321_);
lean_dec_ref(v_preds_1341_);
if (lean_obj_tag(v___x_1342_) == 1)
{
lean_object* v_val_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1395_; 
v_val_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1395_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_val_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1395_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_argumentSorts_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v_argumentSorts_1347_ = lean_ctor_get(v_val_1343_, 0);
lean_inc_ref(v_argumentSorts_1347_);
lean_dec(v_val_1343_);
v___x_1348_ = lean_array_get_size(v_x_1322_);
v___x_1349_ = lean_array_get_size(v_argumentSorts_1347_);
v___x_1350_ = lean_nat_dec_eq(v___x_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_dec_ref(v_argumentSorts_1347_);
lean_dec_ref(v_x_1322_);
v___x_1351_ = lean_box(v___x_1350_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1351_);
v___x_1353_ = v___x_1345_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; size_t v_sz_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
lean_del_object(v___x_1345_);
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = l_Array_toSubarray___redArg(v_argumentSorts_1347_, v___x_1355_, v___x_1349_);
v___x_1357_ = lean_box(0);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___x_1356_);
v_sz_1359_ = lean_array_size(v_x_1322_);
v___x_1360_ = ((size_t)0ULL);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg(v_depth_1320_, v_x_1322_, v_sz_1359_, v___x_1360_, v___x_1358_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec_ref(v_x_1322_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1386_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1386_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1386_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_fst_1366_; 
v_fst_1366_ = lean_ctor_get(v_a_1362_, 0);
lean_inc(v_fst_1366_);
lean_dec(v_a_1362_);
if (lean_obj_tag(v_fst_1366_) == 0)
{
lean_object* v___x_1367_; lean_object* v_usedElements_1368_; lean_object* v_cache_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1381_; 
v___x_1367_ = lean_st_ref_take(v___y_1325_);
v_usedElements_1368_ = lean_ctor_get(v___x_1367_, 0);
v_cache_1369_ = lean_ctor_get(v___x_1367_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1371_ = v___x_1367_;
v_isShared_1372_ = v_isSharedCheck_1381_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_cache_1369_);
lean_inc(v_usedElements_1368_);
lean_dec(v___x_1367_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1381_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_usedElements_1368_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_cache_1369_);
v___x_1374_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
lean_ctor_set_uint8(v___x_1374_, sizeof(void*)*2, v___x_1350_);
v___x_1375_ = lean_st_ref_put(v___y_1325_, v___x_1374_);
v___x_1376_ = lean_box(v___x_1350_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1376_);
v___x_1378_ = v___x_1364_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
else
{
lean_object* v_val_1382_; lean_object* v___x_1384_; 
v_val_1382_ = lean_ctor_get(v_fst_1366_, 0);
lean_inc(v_val_1382_);
lean_dec_ref_known(v_fst_1366_, 1);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v_val_1382_);
v___x_1384_ = v___x_1364_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_val_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
v_a_1387_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1361_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1361_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
}
else
{
uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec(v___x_1342_);
lean_dec_ref(v_x_1322_);
v___x_1396_ = 0;
v___x_1397_ = lean_box(v___x_1396_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
return v___x_1398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__1___boxed(lean_object* v_depth_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_, lean_object* v_x_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__1(v_depth_1399_, v_x_1400_, v_x_1401_, v_x_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v_depth_1399_);
return v_res_1413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp___closed__0(void){
_start:
{
lean_object* v___x_1414_; lean_object* v_dummy_1415_; 
v___x_1414_ = lean_box(0);
v_dummy_1415_ = l_Lean_Expr_sort___override(v___x_1414_);
return v_dummy_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp(lean_object* v_e_1416_, lean_object* v_depth_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v_dummy_1428_; lean_object* v_nargs_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_dummy_1428_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp___closed__0);
v_nargs_1429_ = l_Lean_Expr_getAppNumArgs(v_e_1416_);
lean_inc(v_nargs_1429_);
v___x_1430_ = lean_mk_array(v_nargs_1429_, v_dummy_1428_);
v___x_1431_ = lean_unsigned_to_nat(1u);
v___x_1432_ = lean_nat_sub(v_nargs_1429_, v___x_1431_);
lean_dec(v_nargs_1429_);
v___x_1433_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__1(v_depth_1417_, v_e_1416_, v___x_1430_, v___x_1432_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp___boxed(lean_object* v_e_1434_, lean_object* v_depth_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp(v_e_1434_, v_depth_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_depth_1435_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0(lean_object* v_depth_1447_, lean_object* v_as_1448_, size_t v_sz_1449_, size_t v_i_1450_, lean_object* v_b_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___redArg(v_depth_1447_, v_as_1448_, v_sz_1449_, v_i_1450_, v_b_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0___boxed(lean_object* v_depth_1463_, lean_object* v_as_1464_, lean_object* v_sz_1465_, lean_object* v_i_1466_, lean_object* v_b_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
size_t v_sz_boxed_1478_; size_t v_i_boxed_1479_; lean_object* v_res_1480_; 
v_sz_boxed_1478_ = lean_unbox_usize(v_sz_1465_);
lean_dec(v_sz_1465_);
v_i_boxed_1479_ = lean_unbox_usize(v_i_1466_);
lean_dec(v_i_1466_);
v_res_1480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp_spec__0(v_depth_1463_, v_as_1464_, v_sz_boxed_1478_, v_i_boxed_1479_, v_b_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec_ref(v_as_1464_);
lean_dec(v_depth_1463_);
return v_res_1480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__2(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___f_1486_; 
v___x_1485_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_1486_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1486_, 0, v___x_1485_);
return v___f_1486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__3(void){
_start:
{
lean_object* v___f_1487_; lean_object* v___f_1488_; lean_object* v___f_1489_; 
v___f_1487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__2);
v___f_1488_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_getSort_x3f___redArg___closed__0));
v___f_1489_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1489_, 0, v___f_1488_);
lean_closure_set(v___f_1489_, 1, v___f_1487_);
return v___f_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache(lean_object* v_e_1490_, lean_object* v_depth_1491_, lean_object* v_k_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v___f_1503_; lean_object* v___x_1504_; lean_object* v_cache_1505_; lean_object* v___f_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; uint8_t v___x_1509_; 
v___f_1503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__1));
v___x_1504_ = lean_st_ref_get(v_a_1494_);
v_cache_1505_ = lean_ctor_get(v___x_1504_, 1);
lean_inc_ref(v_cache_1505_);
lean_dec(v___x_1504_);
v___f_1506_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___closed__3);
lean_inc(v_depth_1491_);
lean_inc_ref(v_e_1490_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v_e_1490_);
lean_ctor_set(v___x_1507_, 1, v_depth_1491_);
lean_inc_ref(v___x_1507_);
v___x_1508_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1506_, v___f_1503_, v_cache_1505_, v___x_1507_);
lean_dec_ref(v_cache_1505_);
v___x_1509_ = 1;
if (v___x_1508_ == 0)
{
lean_object* v___x_1510_; 
lean_inc(v_a_1501_);
lean_inc_ref(v_a_1500_);
lean_inc(v_a_1499_);
lean_inc_ref(v_a_1498_);
lean_inc(v_a_1497_);
lean_inc_ref(v_a_1496_);
lean_inc(v_a_1495_);
lean_inc(v_a_1494_);
lean_inc_ref(v_a_1493_);
v___x_1510_ = lean_apply_12(v_k_1492_, v_e_1490_, v_depth_1491_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, lean_box(0));
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; uint8_t v___x_1512_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
v___x_1512_ = lean_unbox(v_a_1511_);
lean_dec(v_a_1511_);
if (v___x_1512_ == 0)
{
lean_dec_ref_known(v___x_1507_, 2);
return v___x_1510_;
}
else
{
lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1534_; 
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v___x_1510_, 0);
lean_dec(v_unused_1535_);
v___x_1514_ = v___x_1510_;
v_isShared_1515_ = v_isSharedCheck_1534_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v___x_1510_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1534_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; uint8_t v_mentionsSort_1517_; lean_object* v_usedElements_1518_; lean_object* v_cache_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1533_; 
v___x_1516_ = lean_st_ref_take(v_a_1494_);
v_mentionsSort_1517_ = lean_ctor_get_uint8(v___x_1516_, sizeof(void*)*2);
v_usedElements_1518_ = lean_ctor_get(v___x_1516_, 0);
v_cache_1519_ = lean_ctor_get(v___x_1516_, 1);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1521_ = v___x_1516_;
v_isShared_1522_ = v_isSharedCheck_1533_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_cache_1519_);
lean_inc(v_usedElements_1518_);
lean_dec(v___x_1516_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1533_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1523_ = lean_box(0);
v___x_1524_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_1506_, v___f_1503_, v_cache_1519_, v___x_1507_, v___x_1523_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1524_);
v___x_1526_ = v___x_1521_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_usedElements_1518_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v___x_1524_);
lean_ctor_set_uint8(v_reuseFailAlloc_1532_, sizeof(void*)*2, v_mentionsSort_1517_);
v___x_1526_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1527_ = lean_st_ref_put(v_a_1494_, v___x_1526_);
v___x_1528_ = lean_box(v___x_1509_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1528_);
v___x_1530_ = v___x_1514_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_1507_, 2);
return v___x_1510_;
}
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec_ref_known(v___x_1507_, 2);
lean_dec_ref(v_k_1492_);
lean_dec(v_depth_1491_);
lean_dec_ref(v_e_1490_);
v___x_1536_ = lean_box(v___x_1509_);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache___boxed(lean_object* v_e_1538_, lean_object* v_depth_1539_, lean_object* v_k_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_withCheckCache(v_e_1538_, v_depth_1539_, v_k_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
lean_dec(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___redArg(lean_object* v_e_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
if (lean_obj_tag(v_e_1552_) == 1)
{
lean_object* v_fvarId_1557_; lean_object* v___x_1558_; 
v_fvarId_1557_ = lean_ctor_get(v_e_1552_, 0);
lean_inc(v_fvarId_1557_);
lean_dec_ref_known(v_e_1552_, 1);
v___x_1558_ = l_Lean_FVarId_getType___redArg(v_fvarId_1557_, v_a_1553_, v_a_1554_, v_a_1555_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1568_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1568_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1568_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
uint8_t v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1563_ = l_Lean_Expr_isProp(v_a_1559_);
lean_dec(v_a_1559_);
v___x_1564_ = lean_box(v___x_1563_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1564_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_a_1569_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1558_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1558_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
uint8_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec_ref(v_e_1552_);
v___x_1577_ = 0;
v___x_1578_ = lean_box(v___x_1577_);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___redArg___boxed(lean_object* v_e_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___redArg(v_e_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec_ref(v_a_1581_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom(lean_object* v_e_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___redArg(v_e_1586_, v_a_1592_, v_a_1594_, v_a_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___boxed(lean_object* v_e_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom(v_e_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg(lean_object* v_e_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
if (lean_obj_tag(v_e_1612_) == 1)
{
lean_object* v_fvarId_1617_; lean_object* v___x_1618_; 
v_fvarId_1617_ = lean_ctor_get(v_e_1612_, 0);
lean_inc(v_fvarId_1617_);
lean_dec_ref_known(v_e_1612_, 1);
v___x_1618_ = l_Lean_FVarId_getType___redArg(v_fvarId_1617_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1629_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1629_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1629_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg___closed__0));
v___x_1624_ = l_Lean_Expr_isConstOf(v_a_1619_, v___x_1623_);
lean_dec(v_a_1619_);
v___x_1625_ = lean_box(v___x_1624_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1625_);
v___x_1627_ = v___x_1621_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
v_a_1630_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1618_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1618_);
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
else
{
uint8_t v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec_ref(v_e_1612_);
v___x_1638_ = 0;
v___x_1639_ = lean_box(v___x_1638_);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg___boxed(lean_object* v_e_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg(v_e_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom(lean_object* v_e_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg(v_e_1647_, v_a_1653_, v_a_1655_, v_a_1656_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___boxed(lean_object* v_e_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom(v_e_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
return v_res_1670_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg(lean_object* v_a_1671_, lean_object* v_x_1672_){
_start:
{
if (lean_obj_tag(v_x_1672_) == 0)
{
uint8_t v___x_1673_; 
v___x_1673_ = 0;
return v___x_1673_;
}
else
{
lean_object* v_key_1674_; lean_object* v_tail_1675_; lean_object* v_fst_1676_; lean_object* v_snd_1677_; lean_object* v_fst_1678_; lean_object* v_snd_1679_; size_t v___x_1680_; size_t v___x_1681_; uint8_t v___x_1682_; 
v_key_1674_ = lean_ctor_get(v_x_1672_, 0);
v_tail_1675_ = lean_ctor_get(v_x_1672_, 2);
v_fst_1676_ = lean_ctor_get(v_key_1674_, 0);
v_snd_1677_ = lean_ctor_get(v_key_1674_, 1);
v_fst_1678_ = lean_ctor_get(v_a_1671_, 0);
v_snd_1679_ = lean_ctor_get(v_a_1671_, 1);
v___x_1680_ = lean_ptr_addr(v_fst_1676_);
v___x_1681_ = lean_ptr_addr(v_fst_1678_);
v___x_1682_ = lean_usize_dec_eq(v___x_1680_, v___x_1681_);
if (v___x_1682_ == 0)
{
v_x_1672_ = v_tail_1675_;
goto _start;
}
else
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_nat_dec_eq(v_snd_1677_, v_snd_1679_);
if (v___x_1684_ == 0)
{
v_x_1672_ = v_tail_1675_;
goto _start;
}
else
{
return v___x_1684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg___boxed(lean_object* v_a_1686_, lean_object* v_x_1687_){
_start:
{
uint8_t v_res_1688_; lean_object* v_r_1689_; 
v_res_1688_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg(v_a_1686_, v_x_1687_);
lean_dec(v_x_1687_);
lean_dec_ref(v_a_1686_);
v_r_1689_ = lean_box(v_res_1688_);
return v_r_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* v_x_1690_, lean_object* v_x_1691_){
_start:
{
if (lean_obj_tag(v_x_1691_) == 0)
{
return v_x_1690_;
}
else
{
lean_object* v_key_1692_; lean_object* v_value_1693_; lean_object* v_tail_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1724_; 
v_key_1692_ = lean_ctor_get(v_x_1691_, 0);
v_value_1693_ = lean_ctor_get(v_x_1691_, 1);
v_tail_1694_ = lean_ctor_get(v_x_1691_, 2);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_x_1691_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1696_ = v_x_1691_;
v_isShared_1697_ = v_isSharedCheck_1724_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_tail_1694_);
lean_inc(v_value_1693_);
lean_inc(v_key_1692_);
lean_dec(v_x_1691_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1724_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_fst_1698_; lean_object* v_snd_1699_; lean_object* v___x_1700_; size_t v___x_1701_; size_t v___x_1702_; size_t v___x_1703_; uint64_t v___x_1704_; uint64_t v___x_1705_; uint64_t v___x_1706_; uint64_t v___x_1707_; uint64_t v___x_1708_; uint64_t v_fold_1709_; uint64_t v___x_1710_; uint64_t v___x_1711_; uint64_t v___x_1712_; size_t v___x_1713_; size_t v___x_1714_; size_t v___x_1715_; size_t v___x_1716_; size_t v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
v_fst_1698_ = lean_ctor_get(v_key_1692_, 0);
v_snd_1699_ = lean_ctor_get(v_key_1692_, 1);
v___x_1700_ = lean_array_get_size(v_x_1690_);
v___x_1701_ = lean_ptr_addr(v_fst_1698_);
v___x_1702_ = ((size_t)3ULL);
v___x_1703_ = lean_usize_shift_right(v___x_1701_, v___x_1702_);
v___x_1704_ = lean_usize_to_uint64(v___x_1703_);
v___x_1705_ = lean_uint64_of_nat(v_snd_1699_);
v___x_1706_ = lean_uint64_mix_hash(v___x_1704_, v___x_1705_);
v___x_1707_ = 32ULL;
v___x_1708_ = lean_uint64_shift_right(v___x_1706_, v___x_1707_);
v_fold_1709_ = lean_uint64_xor(v___x_1706_, v___x_1708_);
v___x_1710_ = 16ULL;
v___x_1711_ = lean_uint64_shift_right(v_fold_1709_, v___x_1710_);
v___x_1712_ = lean_uint64_xor(v_fold_1709_, v___x_1711_);
v___x_1713_ = lean_uint64_to_usize(v___x_1712_);
v___x_1714_ = lean_usize_of_nat(v___x_1700_);
v___x_1715_ = ((size_t)1ULL);
v___x_1716_ = lean_usize_sub(v___x_1714_, v___x_1715_);
v___x_1717_ = lean_usize_land(v___x_1713_, v___x_1716_);
v___x_1718_ = lean_array_uget_borrowed(v_x_1690_, v___x_1717_);
lean_inc(v___x_1718_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 2, v___x_1718_);
v___x_1720_ = v___x_1696_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_key_1692_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_value_1693_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_array_uset(v_x_1690_, v___x_1717_, v___x_1720_);
v_x_1690_ = v___x_1721_;
v_x_1691_ = v_tail_1694_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6___redArg(lean_object* v_i_1725_, lean_object* v_source_1726_, lean_object* v_target_1727_){
_start:
{
lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1728_ = lean_array_get_size(v_source_1726_);
v___x_1729_ = lean_nat_dec_lt(v_i_1725_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_dec_ref(v_source_1726_);
lean_dec(v_i_1725_);
return v_target_1727_;
}
else
{
lean_object* v_es_1730_; lean_object* v___x_1731_; lean_object* v_source_1732_; lean_object* v_target_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_es_1730_ = lean_array_fget(v_source_1726_, v_i_1725_);
v___x_1731_ = lean_box(0);
v_source_1732_ = lean_array_fset(v_source_1726_, v_i_1725_, v___x_1731_);
v_target_1733_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6_spec__7___redArg(v_target_1727_, v_es_1730_);
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_nat_add(v_i_1725_, v___x_1734_);
lean_dec(v_i_1725_);
v_i_1725_ = v___x_1735_;
v_source_1726_ = v_source_1732_;
v_target_1727_ = v_target_1733_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4___redArg(lean_object* v_data_1737_){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v_nbuckets_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1738_ = lean_array_get_size(v_data_1737_);
v___x_1739_ = lean_unsigned_to_nat(2u);
v_nbuckets_1740_ = lean_nat_mul(v___x_1738_, v___x_1739_);
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = lean_box(0);
v___x_1743_ = lean_mk_array(v_nbuckets_1740_, v___x_1742_);
v___x_1744_ = lean_array_propagate_mark(v_data_1737_, v___x_1743_);
v___x_1745_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6___redArg(v___x_1741_, v_data_1737_, v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2___redArg(lean_object* v_m_1746_, lean_object* v_a_1747_, lean_object* v_b_1748_){
_start:
{
lean_object* v_size_1749_; lean_object* v_buckets_1750_; lean_object* v_fst_1751_; lean_object* v_snd_1752_; lean_object* v___x_1753_; size_t v___x_1754_; size_t v___x_1755_; size_t v___x_1756_; uint64_t v___x_1757_; uint64_t v___x_1758_; uint64_t v___x_1759_; uint64_t v___x_1760_; uint64_t v___x_1761_; uint64_t v_fold_1762_; uint64_t v___x_1763_; uint64_t v___x_1764_; uint64_t v___x_1765_; size_t v___x_1766_; size_t v___x_1767_; size_t v___x_1768_; size_t v___x_1769_; size_t v___x_1770_; lean_object* v_bkt_1771_; uint8_t v___x_1772_; 
v_size_1749_ = lean_ctor_get(v_m_1746_, 0);
v_buckets_1750_ = lean_ctor_get(v_m_1746_, 1);
v_fst_1751_ = lean_ctor_get(v_a_1747_, 0);
v_snd_1752_ = lean_ctor_get(v_a_1747_, 1);
v___x_1753_ = lean_array_get_size(v_buckets_1750_);
v___x_1754_ = lean_ptr_addr(v_fst_1751_);
v___x_1755_ = ((size_t)3ULL);
v___x_1756_ = lean_usize_shift_right(v___x_1754_, v___x_1755_);
v___x_1757_ = lean_usize_to_uint64(v___x_1756_);
v___x_1758_ = lean_uint64_of_nat(v_snd_1752_);
v___x_1759_ = lean_uint64_mix_hash(v___x_1757_, v___x_1758_);
v___x_1760_ = 32ULL;
v___x_1761_ = lean_uint64_shift_right(v___x_1759_, v___x_1760_);
v_fold_1762_ = lean_uint64_xor(v___x_1759_, v___x_1761_);
v___x_1763_ = 16ULL;
v___x_1764_ = lean_uint64_shift_right(v_fold_1762_, v___x_1763_);
v___x_1765_ = lean_uint64_xor(v_fold_1762_, v___x_1764_);
v___x_1766_ = lean_uint64_to_usize(v___x_1765_);
v___x_1767_ = lean_usize_of_nat(v___x_1753_);
v___x_1768_ = ((size_t)1ULL);
v___x_1769_ = lean_usize_sub(v___x_1767_, v___x_1768_);
v___x_1770_ = lean_usize_land(v___x_1766_, v___x_1769_);
v_bkt_1771_ = lean_array_uget_borrowed(v_buckets_1750_, v___x_1770_);
v___x_1772_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg(v_a_1747_, v_bkt_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1793_; 
lean_inc_ref(v_buckets_1750_);
lean_inc(v_size_1749_);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_m_1746_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; lean_object* v_unused_1795_; 
v_unused_1794_ = lean_ctor_get(v_m_1746_, 1);
lean_dec(v_unused_1794_);
v_unused_1795_ = lean_ctor_get(v_m_1746_, 0);
lean_dec(v_unused_1795_);
v___x_1774_ = v_m_1746_;
v_isShared_1775_ = v_isSharedCheck_1793_;
goto v_resetjp_1773_;
}
else
{
lean_dec(v_m_1746_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1793_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; lean_object* v_size_x27_1777_; lean_object* v___x_1778_; lean_object* v_buckets_x27_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1776_ = lean_unsigned_to_nat(1u);
v_size_x27_1777_ = lean_nat_add(v_size_1749_, v___x_1776_);
lean_dec(v_size_1749_);
lean_inc(v_bkt_1771_);
v___x_1778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1778_, 0, v_a_1747_);
lean_ctor_set(v___x_1778_, 1, v_b_1748_);
lean_ctor_set(v___x_1778_, 2, v_bkt_1771_);
v_buckets_x27_1779_ = lean_array_uset(v_buckets_1750_, v___x_1770_, v___x_1778_);
v___x_1780_ = lean_unsigned_to_nat(4u);
v___x_1781_ = lean_nat_mul(v_size_x27_1777_, v___x_1780_);
v___x_1782_ = lean_unsigned_to_nat(3u);
v___x_1783_ = lean_nat_div(v___x_1781_, v___x_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_array_get_size(v_buckets_x27_1779_);
v___x_1785_ = lean_nat_dec_le(v___x_1783_, v___x_1784_);
lean_dec(v___x_1783_);
if (v___x_1785_ == 0)
{
lean_object* v_val_1786_; lean_object* v___x_1788_; 
v_val_1786_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4___redArg(v_buckets_x27_1779_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v_val_1786_);
lean_ctor_set(v___x_1774_, 0, v_size_x27_1777_);
v___x_1788_ = v___x_1774_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_size_x27_1777_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_val_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
else
{
lean_object* v___x_1791_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v_buckets_x27_1779_);
lean_ctor_set(v___x_1774_, 0, v_size_x27_1777_);
v___x_1791_ = v___x_1774_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_size_x27_1777_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_buckets_x27_1779_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_dec(v_b_1748_);
lean_dec_ref(v_a_1747_);
return v_m_1746_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg(lean_object* v_m_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_buckets_1798_; lean_object* v_fst_1799_; lean_object* v_snd_1800_; lean_object* v___x_1801_; size_t v___x_1802_; size_t v___x_1803_; size_t v___x_1804_; uint64_t v___x_1805_; uint64_t v___x_1806_; uint64_t v___x_1807_; uint64_t v___x_1808_; uint64_t v___x_1809_; uint64_t v_fold_1810_; uint64_t v___x_1811_; uint64_t v___x_1812_; uint64_t v___x_1813_; size_t v___x_1814_; size_t v___x_1815_; size_t v___x_1816_; size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v_buckets_1798_ = lean_ctor_get(v_m_1796_, 1);
v_fst_1799_ = lean_ctor_get(v_a_1797_, 0);
v_snd_1800_ = lean_ctor_get(v_a_1797_, 1);
v___x_1801_ = lean_array_get_size(v_buckets_1798_);
v___x_1802_ = lean_ptr_addr(v_fst_1799_);
v___x_1803_ = ((size_t)3ULL);
v___x_1804_ = lean_usize_shift_right(v___x_1802_, v___x_1803_);
v___x_1805_ = lean_usize_to_uint64(v___x_1804_);
v___x_1806_ = lean_uint64_of_nat(v_snd_1800_);
v___x_1807_ = lean_uint64_mix_hash(v___x_1805_, v___x_1806_);
v___x_1808_ = 32ULL;
v___x_1809_ = lean_uint64_shift_right(v___x_1807_, v___x_1808_);
v_fold_1810_ = lean_uint64_xor(v___x_1807_, v___x_1809_);
v___x_1811_ = 16ULL;
v___x_1812_ = lean_uint64_shift_right(v_fold_1810_, v___x_1811_);
v___x_1813_ = lean_uint64_xor(v_fold_1810_, v___x_1812_);
v___x_1814_ = lean_uint64_to_usize(v___x_1813_);
v___x_1815_ = lean_usize_of_nat(v___x_1801_);
v___x_1816_ = ((size_t)1ULL);
v___x_1817_ = lean_usize_sub(v___x_1815_, v___x_1816_);
v___x_1818_ = lean_usize_land(v___x_1814_, v___x_1817_);
v___x_1819_ = lean_array_uget_borrowed(v_buckets_1798_, v___x_1818_);
v___x_1820_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg(v_a_1797_, v___x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg___boxed(lean_object* v_m_1821_, lean_object* v_a_1822_){
_start:
{
uint8_t v_res_1823_; lean_object* v_r_1824_; 
v_res_1823_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg(v_m_1821_, v_a_1822_);
lean_dec_ref(v_a_1822_);
lean_dec_ref(v_m_1821_);
v_r_1824_ = lean_box(v_res_1823_);
return v_r_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go(lean_object* v_e_1886_, lean_object* v_depth_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v_p_1917_; lean_object* v_q_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; 
if (lean_obj_tag(v_e_1886_) == 7)
{
lean_object* v_binderType_1932_; lean_object* v_body_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v_binderType_1932_ = lean_ctor_get(v_e_1886_, 1);
lean_inc_ref(v_binderType_1932_);
v_body_1933_ = lean_ctor_get(v_e_1886_, 2);
lean_inc_ref(v_body_1933_);
lean_dec_ref_known(v_e_1886_, 3);
v___x_1934_ = lean_unsigned_to_nat(0u);
v___x_1935_ = lean_expr_has_loose_bvar(v_body_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; 
lean_inc(v_depth_1887_);
v___x_1936_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_binderType_1932_, v_depth_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; uint8_t v___x_1938_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v___x_1938_ = lean_unbox(v_a_1937_);
if (v___x_1938_ == 0)
{
lean_dec_ref(v_body_1933_);
lean_dec(v_depth_1887_);
return v___x_1936_;
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec_ref_known(v___x_1936_, 1);
v___x_1939_ = lean_unsigned_to_nat(1u);
v___x_1940_ = lean_nat_add(v_depth_1887_, v___x_1939_);
lean_dec(v_depth_1887_);
v___x_1941_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_body_1933_, v___x_1940_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
return v___x_1941_;
}
}
else
{
lean_dec_ref(v_body_1933_);
lean_dec(v_depth_1887_);
return v___x_1936_;
}
}
else
{
uint8_t v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec_ref(v_body_1933_);
lean_dec_ref(v_binderType_1932_);
lean_dec(v_depth_1887_);
v___x_1942_ = 0;
v___x_1943_ = lean_box(v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
}
else
{
lean_object* v___x_1945_; 
lean_inc_ref(v_e_1886_);
v___x_1945_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1886_, v_a_1894_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v___x_1945_, 1);
v___x_1947_ = l_Lean_Expr_cleanupAnnotations(v_a_1946_);
lean_dec(v_a_1946_);
v___x_1948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__1));
v___x_1949_ = l_Lean_Expr_isConstOf(v___x_1947_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__3));
v___x_1951_ = l_Lean_Expr_isConstOf(v___x_1947_, v___x_1950_);
if (v___x_1951_ == 0)
{
uint8_t v___x_1952_; 
v___x_1952_ = l_Lean_Expr_isApp(v___x_1947_);
if (v___x_1952_ == 0)
{
lean_dec_ref(v___x_1947_);
v___y_1903_ = v_a_1888_;
v___y_1904_ = v_a_1889_;
v___y_1905_ = v_a_1890_;
v___y_1906_ = v_a_1891_;
v___y_1907_ = v_a_1892_;
v___y_1908_ = v_a_1893_;
v___y_1909_ = v_a_1894_;
v___y_1910_ = v_a_1895_;
v___y_1911_ = v_a_1896_;
goto v___jp_1902_;
}
else
{
lean_object* v_arg_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v_arg_1953_ = lean_ctor_get(v___x_1947_, 1);
lean_inc_ref(v_arg_1953_);
v___x_1954_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1947_);
lean_dec_ref(v___x_1947_);
v___x_1955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__5));
v___x_1956_ = l_Lean_Expr_isConstOf(v___x_1954_, v___x_1955_);
if (v___x_1956_ == 0)
{
uint8_t v___x_1957_; 
v___x_1957_ = l_Lean_Expr_isApp(v___x_1954_);
if (v___x_1957_ == 0)
{
lean_dec_ref(v___x_1954_);
lean_dec_ref(v_arg_1953_);
v___y_1903_ = v_a_1888_;
v___y_1904_ = v_a_1889_;
v___y_1905_ = v_a_1890_;
v___y_1906_ = v_a_1891_;
v___y_1907_ = v_a_1892_;
v___y_1908_ = v_a_1893_;
v___y_1909_ = v_a_1894_;
v___y_1910_ = v_a_1895_;
v___y_1911_ = v_a_1896_;
goto v___jp_1902_;
}
else
{
lean_object* v_arg_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v_arg_1958_ = lean_ctor_get(v___x_1954_, 1);
lean_inc_ref(v_arg_1958_);
v___x_1959_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1954_);
lean_dec_ref(v___x_1954_);
v___x_1960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__7));
v___x_1961_ = l_Lean_Expr_isConstOf(v___x_1959_, v___x_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__9));
v___x_1963_ = l_Lean_Expr_isConstOf(v___x_1959_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__11));
v___x_1965_ = l_Lean_Expr_isConstOf(v___x_1959_, v___x_1964_);
if (v___x_1965_ == 0)
{
uint8_t v___x_1966_; 
v___x_1966_ = l_Lean_Expr_isApp(v___x_1959_);
if (v___x_1966_ == 0)
{
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_arg_1958_);
lean_dec_ref(v_arg_1953_);
v___y_1903_ = v_a_1888_;
v___y_1904_ = v_a_1889_;
v___y_1905_ = v_a_1890_;
v___y_1906_ = v_a_1891_;
v___y_1907_ = v_a_1892_;
v___y_1908_ = v_a_1893_;
v___y_1909_ = v_a_1894_;
v___y_1910_ = v_a_1895_;
v___y_1911_ = v_a_1896_;
goto v___jp_1902_;
}
else
{
lean_object* v_arg_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v_arg_1967_ = lean_ctor_get(v___x_1959_, 1);
lean_inc_ref(v_arg_1967_);
v___x_1968_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1959_);
lean_dec_ref(v___x_1959_);
v___x_1969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___closed__13));
v___x_1970_ = l_Lean_Expr_isConstOf(v___x_1968_, v___x_1969_);
if (v___x_1970_ == 0)
{
uint8_t v___x_1971_; 
v___x_1971_ = l_Lean_Expr_isApp(v___x_1968_);
if (v___x_1971_ == 0)
{
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_arg_1967_);
lean_dec_ref(v_arg_1958_);
lean_dec_ref(v_arg_1953_);
v___y_1903_ = v_a_1888_;
v___y_1904_ = v_a_1889_;
v___y_1905_ = v_a_1890_;
v___y_1906_ = v_a_1891_;
v___y_1907_ = v_a_1892_;
v___y_1908_ = v_a_1893_;
v___y_1909_ = v_a_1894_;
v___y_1910_ = v_a_1895_;
v___y_1911_ = v_a_1896_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1972_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1968_);
v___x_1973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__16));
v___x_1974_ = l_Lean_Expr_isConstOf(v___x_1972_, v___x_1973_);
if (v___x_1974_ == 0)
{
uint8_t v___x_1975_; 
lean_dec_ref(v_arg_1967_);
v___x_1975_ = l_Lean_Expr_isApp(v___x_1972_);
if (v___x_1975_ == 0)
{
lean_dec_ref(v___x_1972_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_arg_1958_);
lean_dec_ref(v_arg_1953_);
v___y_1903_ = v_a_1888_;
v___y_1904_ = v_a_1889_;
v___y_1905_ = v_a_1890_;
v___y_1906_ = v_a_1891_;
v___y_1907_ = v_a_1892_;
v___y_1908_ = v_a_1893_;
v___y_1909_ = v_a_1894_;
v___y_1910_ = v_a_1895_;
v___y_1911_ = v_a_1896_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1976_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1972_);
lean_dec_ref(v___x_1972_);
v___x_1977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__21));
v___x_1978_ = l_Lean_Expr_isConstOf(v___x_1976_, v___x_1977_);
lean_dec_ref(v___x_1976_);
if (v___x_1978_ == 0)
{
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_arg_1958_);
lean_dec_ref(v_arg_1953_);
v___y_1903_ = v_a_1888_;
v___y_1904_ = v_a_1889_;
v___y_1905_ = v_a_1890_;
v___y_1906_ = v_a_1891_;
v___y_1907_ = v_a_1892_;
v___y_1908_ = v_a_1893_;
v___y_1909_ = v_a_1894_;
v___y_1910_ = v_a_1895_;
v___y_1911_ = v_a_1896_;
goto v___jp_1902_;
}
else
{
lean_object* v_arg_1979_; lean_object* v___x_1980_; 
lean_dec_ref(v_e_1886_);
v_arg_1979_ = lean_ctor_get(v___x_1968_, 1);
lean_inc_ref(v_arg_1979_);
lean_dec_ref(v___x_1968_);
lean_inc(v_depth_1887_);
v___x_1980_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1979_, v_depth_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; uint8_t v___x_1982_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v___x_1982_ = lean_unbox(v_a_1981_);
if (v___x_1982_ == 0)
{
lean_dec_ref(v_arg_1958_);
lean_dec_ref(v_arg_1953_);
lean_dec(v_depth_1887_);
return v___x_1980_;
}
else
{
lean_object* v___x_1983_; 
lean_dec_ref_known(v___x_1980_, 1);
lean_inc(v_depth_1887_);
v___x_1983_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1958_, v_depth_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; uint8_t v___x_1985_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v___x_1985_ = lean_unbox(v_a_1984_);
if (v___x_1985_ == 0)
{
lean_dec_ref(v_arg_1953_);
lean_dec(v_depth_1887_);
return v___x_1983_;
}
else
{
lean_object* v___x_1986_; 
lean_dec_ref_known(v___x_1983_, 1);
v___x_1986_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1953_, v_depth_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
return v___x_1986_;
}
}
else
{
lean_dec_ref(v_arg_1953_);
lean_dec(v_depth_1887_);
return v___x_1983_;
}
}
}
else
{
lean_dec_ref(v_arg_1958_);
lean_dec_ref(v_arg_1953_);
lean_dec(v_depth_1887_);
return v___x_1980_;
}
}
}
}
else
{
lean_object* v___x_1987_; 
lean_dec_ref(v___x_1972_);
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_e_1886_);
lean_inc(v_depth_1887_);
v___x_1987_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_1967_, v_depth_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; uint8_t v___x_1989_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v___x_1989_ = lean_unbox(v_a_1988_);
if (v___x_1989_ == 0)
{
lean_dec_ref(v_arg_1958_);
lean_dec_ref(v_arg_1953_);
lean_dec(v_depth_1887_);
return v___x_1987_;
}
else
{
lean_object* v___x_1990_; 
lean_dec_ref_known(v___x_1987_, 1);
lean_inc(v_depth_1887_);
v___x_1990_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1958_, v_depth_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; uint8_t v___x_1992_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v___x_1992_ = lean_unbox(v_a_1991_);
if (v___x_1992_ == 0)
{
lean_dec_ref(v_arg_1953_);
lean_dec(v_depth_1887_);
return v___x_1990_;
}
else
{
lean_object* v___x_1993_; 
lean_dec_ref_known(v___x_1990_, 1);
v___x_1993_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1953_, v_depth_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
return v___x_1993_;
}
}
else
{
lean_dec_ref(v_arg_1953_);
lean_dec(v_depth_1887_);
return v___x_1990_;
}
}
}
else
{
lean_dec_ref(v_arg_1958_);
lean_dec_ref(v_arg_1953_);
lean_dec(v_depth_1887_);
return v___x_1987_;
}
}
}
}
else
{
uint8_t v___x_1994_; 
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_e_1886_);
v___x_1994_ = l_Lean_Expr_isProp(v_arg_1967_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg___closed__0));
v___x_1996_ = l_Lean_Expr_isConstOf(v_arg_1967_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
v___x_1997_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkEq___redArg(v_arg_1967_, v_arg_1958_, v_arg_1953_, v_depth_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
lean_dec(v_depth_1887_);
lean_dec_ref(v_arg_1967_);
return v___x_1997_;
}
else
{
lean_object* v___x_1998_; 
lean_dec_ref(v_arg_1967_);
lean_inc(v_depth_1887_);
v___x_1998_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_1958_, v_depth_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; uint8_t v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v___x_2000_ = lean_unbox(v_a_1999_);
if (v___x_2000_ == 0)
{
lean_dec_ref(v_arg_1953_);
lean_dec(v_depth_1887_);
return v___x_1998_;
}
else
{
lean_object* v___x_2001_; 
lean_dec_ref_known(v___x_1998_, 1);
v___x_2001_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_1953_, v_depth_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
return v___x_2001_;
}
}
else
{
lean_dec_ref(v_arg_1953_);
lean_dec(v_depth_1887_);
return v___x_1998_;
}
}
}
else
{
lean_object* v___x_2002_; 
lean_dec_ref(v_arg_1967_);
lean_inc(v_depth_1887_);
v___x_2002_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1958_, v_depth_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; uint8_t v___x_2004_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v___x_2004_ = lean_unbox(v_a_2003_);
if (v___x_2004_ == 0)
{
lean_dec_ref(v_arg_1953_);
lean_dec(v_depth_1887_);
return v___x_2002_;
}
else
{
lean_object* v___x_2005_; 
lean_dec_ref_known(v___x_2002_, 1);
v___x_2005_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1953_, v_depth_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
return v___x_2005_;
}
}
else
{
lean_dec_ref(v_arg_1953_);
lean_dec(v_depth_1887_);
return v___x_2002_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_e_1886_);
v_p_1917_ = v_arg_1958_;
v_q_1918_ = v_arg_1953_;
v___y_1919_ = v_a_1888_;
v___y_1920_ = v_a_1889_;
v___y_1921_ = v_a_1890_;
v___y_1922_ = v_a_1891_;
v___y_1923_ = v_a_1892_;
v___y_1924_ = v_a_1893_;
v___y_1925_ = v_a_1894_;
v___y_1926_ = v_a_1895_;
v___y_1927_ = v_a_1896_;
goto v___jp_1916_;
}
}
else
{
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_e_1886_);
v_p_1917_ = v_arg_1958_;
v_q_1918_ = v_arg_1953_;
v___y_1919_ = v_a_1888_;
v___y_1920_ = v_a_1889_;
v___y_1921_ = v_a_1890_;
v___y_1922_ = v_a_1891_;
v___y_1923_ = v_a_1892_;
v___y_1924_ = v_a_1893_;
v___y_1925_ = v_a_1894_;
v___y_1926_ = v_a_1895_;
v___y_1927_ = v_a_1896_;
goto v___jp_1916_;
}
}
else
{
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_e_1886_);
v_p_1917_ = v_arg_1958_;
v_q_1918_ = v_arg_1953_;
v___y_1919_ = v_a_1888_;
v___y_1920_ = v_a_1889_;
v___y_1921_ = v_a_1890_;
v___y_1922_ = v_a_1891_;
v___y_1923_ = v_a_1892_;
v___y_1924_ = v_a_1893_;
v___y_1925_ = v_a_1894_;
v___y_1926_ = v_a_1895_;
v___y_1927_ = v_a_1896_;
goto v___jp_1916_;
}
}
}
else
{
lean_object* v___x_2006_; 
lean_dec_ref(v___x_1954_);
lean_dec_ref(v_e_1886_);
v___x_2006_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_1953_, v_depth_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
return v___x_2006_;
}
}
}
else
{
lean_dec_ref(v___x_1947_);
lean_dec(v_depth_1887_);
lean_dec_ref(v_e_1886_);
goto v___jp_1898_;
}
}
else
{
lean_dec_ref(v___x_1947_);
lean_dec(v_depth_1887_);
lean_dec_ref(v_e_1886_);
goto v___jp_1898_;
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec(v_depth_1887_);
lean_dec_ref(v_e_1886_);
v_a_2007_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1945_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1945_);
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
v___jp_1898_:
{
uint8_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = 1;
v___x_1900_ = lean_box(v___x_1899_);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
v___jp_1902_:
{
lean_object* v___x_1912_; 
lean_inc_ref(v_e_1886_);
v___x_1912_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp(v_e_1886_, v_depth_1887_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v_depth_1887_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; uint8_t v___x_1914_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v___x_1914_ = lean_unbox(v_a_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
lean_dec_ref_known(v___x_1912_, 1);
v___x_1915_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_isPropAtom___redArg(v_e_1886_, v___y_1908_, v___y_1910_, v___y_1911_);
return v___x_1915_;
}
else
{
lean_dec_ref(v_e_1886_);
return v___x_1912_;
}
}
else
{
lean_dec_ref(v_e_1886_);
return v___x_1912_;
}
}
v___jp_1916_:
{
lean_object* v___x_1928_; 
lean_inc(v_depth_1887_);
v___x_1928_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_p_1917_, v_depth_1887_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; uint8_t v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v___x_1930_ = lean_unbox(v_a_1929_);
if (v___x_1930_ == 0)
{
lean_dec_ref(v_q_1918_);
lean_dec(v_depth_1887_);
return v___x_1928_;
}
else
{
lean_object* v___x_1931_; 
lean_dec_ref_known(v___x_1928_, 1);
v___x_1931_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_q_1918_, v_depth_1887_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
return v___x_1931_;
}
}
else
{
lean_dec_ref(v_q_1918_);
lean_dec(v_depth_1887_);
return v___x_1928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(lean_object* v_e_2015_, lean_object* v_depth_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v___x_2027_; lean_object* v_cache_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; uint8_t v___x_2031_; 
v___x_2027_ = lean_st_ref_get(v_a_2018_);
v_cache_2028_ = lean_ctor_get(v___x_2027_, 1);
lean_inc_ref(v_cache_2028_);
lean_dec(v___x_2027_);
lean_inc(v_depth_2016_);
lean_inc_ref(v_e_2015_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_e_2015_);
lean_ctor_set(v___x_2029_, 1, v_depth_2016_);
v___x_2030_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg(v_cache_2028_, v___x_2029_);
lean_dec_ref(v_cache_2028_);
v___x_2031_ = 1;
if (v___x_2030_ == 0)
{
lean_object* v___x_2032_; 
v___x_2032_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go(v_e_2015_, v_depth_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; uint8_t v___x_2034_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
v___x_2034_ = lean_unbox(v_a_2033_);
if (v___x_2034_ == 0)
{
lean_dec_ref_known(v___x_2029_, 2);
return v___x_2032_;
}
else
{
lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2056_; 
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v___x_2032_, 0);
lean_dec(v_unused_2057_);
v___x_2036_ = v___x_2032_;
v_isShared_2037_ = v_isSharedCheck_2056_;
goto v_resetjp_2035_;
}
else
{
lean_dec(v___x_2032_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2056_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; uint8_t v_mentionsSort_2039_; lean_object* v_usedElements_2040_; lean_object* v_cache_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2055_; 
v___x_2038_ = lean_st_ref_take(v_a_2018_);
v_mentionsSort_2039_ = lean_ctor_get_uint8(v___x_2038_, sizeof(void*)*2);
v_usedElements_2040_ = lean_ctor_get(v___x_2038_, 0);
v_cache_2041_ = lean_ctor_get(v___x_2038_, 1);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2043_ = v___x_2038_;
v_isShared_2044_ = v_isSharedCheck_2055_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_cache_2041_);
lean_inc(v_usedElements_2040_);
lean_dec(v___x_2038_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2055_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2045_ = lean_box(0);
v___x_2046_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2___redArg(v_cache_2041_, v___x_2029_, v___x_2045_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 1, v___x_2046_);
v___x_2048_ = v___x_2043_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_usedElements_2040_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___x_2046_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*2, v_mentionsSort_2039_);
v___x_2048_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2049_ = lean_st_ref_put(v_a_2018_, v___x_2048_);
v___x_2050_ = lean_box(v___x_2031_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2050_);
v___x_2052_ = v___x_2036_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2029_, 2);
return v___x_2032_;
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec_ref_known(v___x_2029_, 2);
lean_dec(v_depth_2016_);
lean_dec_ref(v_e_2015_);
v___x_2058_ = lean_box(v___x_2031_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go(lean_object* v_e_2060_, lean_object* v_depth_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v_p_2091_; lean_object* v_q_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___x_2106_; 
lean_inc_ref(v_e_2060_);
v___x_2106_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2060_, v_a_2068_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2172_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2172_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2172_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2111_ = l_Lean_Expr_cleanupAnnotations(v_a_2107_);
lean_dec(v_a_2107_);
v___x_2112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__1));
v___x_2113_ = l_Lean_Expr_isConstOf(v___x_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__3));
v___x_2115_ = l_Lean_Expr_isConstOf(v___x_2111_, v___x_2114_);
if (v___x_2115_ == 0)
{
uint8_t v___x_2116_; 
v___x_2116_ = l_Lean_Expr_isApp(v___x_2111_);
if (v___x_2116_ == 0)
{
lean_dec_ref(v___x_2111_);
lean_del_object(v___x_2109_);
v___y_2077_ = v_a_2062_;
v___y_2078_ = v_a_2063_;
v___y_2079_ = v_a_2064_;
v___y_2080_ = v_a_2065_;
v___y_2081_ = v_a_2066_;
v___y_2082_ = v_a_2067_;
v___y_2083_ = v_a_2068_;
v___y_2084_ = v_a_2069_;
v___y_2085_ = v_a_2070_;
goto v___jp_2076_;
}
else
{
lean_object* v_arg_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v_arg_2117_ = lean_ctor_get(v___x_2111_, 1);
lean_inc_ref(v_arg_2117_);
v___x_2118_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2111_);
lean_dec_ref(v___x_2111_);
v___x_2119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__5));
v___x_2120_ = l_Lean_Expr_isConstOf(v___x_2118_, v___x_2119_);
if (v___x_2120_ == 0)
{
uint8_t v___x_2121_; 
v___x_2121_ = l_Lean_Expr_isApp(v___x_2118_);
if (v___x_2121_ == 0)
{
lean_dec_ref(v___x_2118_);
lean_dec_ref(v_arg_2117_);
lean_del_object(v___x_2109_);
v___y_2077_ = v_a_2062_;
v___y_2078_ = v_a_2063_;
v___y_2079_ = v_a_2064_;
v___y_2080_ = v_a_2065_;
v___y_2081_ = v_a_2066_;
v___y_2082_ = v_a_2067_;
v___y_2083_ = v_a_2068_;
v___y_2084_ = v_a_2069_;
v___y_2085_ = v_a_2070_;
goto v___jp_2076_;
}
else
{
lean_object* v_arg_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v_arg_2122_ = lean_ctor_get(v___x_2118_, 1);
lean_inc_ref(v_arg_2122_);
v___x_2123_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2118_);
lean_dec_ref(v___x_2118_);
v___x_2124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__8));
v___x_2125_ = l_Lean_Expr_isConstOf(v___x_2123_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__10));
v___x_2127_ = l_Lean_Expr_isConstOf(v___x_2123_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__12));
v___x_2129_ = l_Lean_Expr_isConstOf(v___x_2123_, v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__14));
v___x_2131_ = l_Lean_Expr_isConstOf(v___x_2123_, v___x_2130_);
if (v___x_2131_ == 0)
{
uint8_t v___x_2132_; 
v___x_2132_ = l_Lean_Expr_isApp(v___x_2123_);
if (v___x_2132_ == 0)
{
lean_dec_ref(v___x_2123_);
lean_dec_ref(v_arg_2122_);
lean_dec_ref(v_arg_2117_);
lean_del_object(v___x_2109_);
v___y_2077_ = v_a_2062_;
v___y_2078_ = v_a_2063_;
v___y_2079_ = v_a_2064_;
v___y_2080_ = v_a_2065_;
v___y_2081_ = v_a_2066_;
v___y_2082_ = v_a_2067_;
v___y_2083_ = v_a_2068_;
v___y_2084_ = v_a_2069_;
v___y_2085_ = v_a_2070_;
goto v___jp_2076_;
}
else
{
lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2133_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2123_);
v___x_2134_ = l_Lean_Expr_isApp(v___x_2133_);
if (v___x_2134_ == 0)
{
lean_dec_ref(v___x_2133_);
lean_dec_ref(v___x_2123_);
lean_dec_ref(v_arg_2122_);
lean_dec_ref(v_arg_2117_);
lean_del_object(v___x_2109_);
v___y_2077_ = v_a_2062_;
v___y_2078_ = v_a_2063_;
v___y_2079_ = v_a_2064_;
v___y_2080_ = v_a_2065_;
v___y_2081_ = v_a_2066_;
v___y_2082_ = v_a_2067_;
v___y_2083_ = v_a_2068_;
v___y_2084_ = v_a_2069_;
v___y_2085_ = v_a_2070_;
goto v___jp_2076_;
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2135_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2133_);
v___x_2136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__16));
v___x_2137_ = l_Lean_Expr_isConstOf(v___x_2135_, v___x_2136_);
if (v___x_2137_ == 0)
{
lean_object* v_arg_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
lean_dec_ref(v___x_2123_);
v_arg_2138_ = lean_ctor_get(v___x_2133_, 1);
lean_inc_ref(v_arg_2138_);
lean_dec_ref(v___x_2133_);
v___x_2139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__19));
v___x_2140_ = l_Lean_Expr_isConstOf(v___x_2135_, v___x_2139_);
if (v___x_2140_ == 0)
{
uint8_t v___x_2141_; 
lean_del_object(v___x_2109_);
v___x_2141_ = l_Lean_Expr_isApp(v___x_2135_);
if (v___x_2141_ == 0)
{
lean_dec_ref(v_arg_2138_);
lean_dec_ref(v___x_2135_);
lean_dec_ref(v_arg_2122_);
lean_dec_ref(v_arg_2117_);
v___y_2077_ = v_a_2062_;
v___y_2078_ = v_a_2063_;
v___y_2079_ = v_a_2064_;
v___y_2080_ = v_a_2065_;
v___y_2081_ = v_a_2066_;
v___y_2082_ = v_a_2067_;
v___y_2083_ = v_a_2068_;
v___y_2084_ = v_a_2069_;
v___y_2085_ = v_a_2070_;
goto v___jp_2076_;
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2142_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2135_);
lean_dec_ref(v___x_2135_);
v___x_2143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___closed__21));
v___x_2144_ = l_Lean_Expr_isConstOf(v___x_2142_, v___x_2143_);
lean_dec_ref(v___x_2142_);
if (v___x_2144_ == 0)
{
lean_dec_ref(v_arg_2138_);
lean_dec_ref(v_arg_2122_);
lean_dec_ref(v_arg_2117_);
v___y_2077_ = v_a_2062_;
v___y_2078_ = v_a_2063_;
v___y_2079_ = v_a_2064_;
v___y_2080_ = v_a_2065_;
v___y_2081_ = v_a_2066_;
v___y_2082_ = v_a_2067_;
v___y_2083_ = v_a_2068_;
v___y_2084_ = v_a_2069_;
v___y_2085_ = v_a_2070_;
goto v___jp_2076_;
}
else
{
lean_object* v___x_2145_; 
lean_dec_ref(v_e_2060_);
lean_inc(v_depth_2061_);
v___x_2145_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_2138_, v_depth_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; uint8_t v___x_2147_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v___x_2147_ = lean_unbox(v_a_2146_);
if (v___x_2147_ == 0)
{
lean_dec_ref(v_arg_2122_);
lean_dec_ref(v_arg_2117_);
lean_dec(v_depth_2061_);
return v___x_2145_;
}
else
{
lean_object* v___x_2148_; 
lean_dec_ref_known(v___x_2145_, 1);
lean_inc(v_depth_2061_);
v___x_2148_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2122_, v_depth_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; uint8_t v___x_2150_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
v___x_2150_ = lean_unbox(v_a_2149_);
if (v___x_2150_ == 0)
{
lean_dec_ref(v_arg_2117_);
lean_dec(v_depth_2061_);
return v___x_2148_;
}
else
{
lean_object* v___x_2151_; 
lean_dec_ref_known(v___x_2148_, 1);
v___x_2151_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2117_, v_depth_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
return v___x_2151_;
}
}
else
{
lean_dec_ref(v_arg_2117_);
lean_dec(v_depth_2061_);
return v___x_2148_;
}
}
}
else
{
lean_dec_ref(v_arg_2122_);
lean_dec_ref(v_arg_2117_);
lean_dec(v_depth_2061_);
return v___x_2145_;
}
}
}
}
else
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
lean_dec_ref(v___x_2135_);
lean_dec_ref(v_e_2060_);
v___x_2152_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg___closed__0));
v___x_2153_ = l_Lean_Expr_isConstOf(v_arg_2138_, v___x_2152_);
lean_dec_ref(v_arg_2138_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
lean_dec_ref(v_arg_2122_);
lean_dec_ref(v_arg_2117_);
lean_dec(v_depth_2061_);
v___x_2154_ = lean_box(v___x_2153_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2154_);
v___x_2156_ = v___x_2109_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
else
{
lean_object* v___x_2158_; 
lean_del_object(v___x_2109_);
lean_inc(v_depth_2061_);
v___x_2158_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2122_, v_depth_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; uint8_t v___x_2160_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v___x_2160_ = lean_unbox(v_a_2159_);
if (v___x_2160_ == 0)
{
lean_dec_ref(v_arg_2117_);
lean_dec(v_depth_2061_);
return v___x_2158_;
}
else
{
lean_object* v___x_2161_; 
lean_dec_ref_known(v___x_2158_, 1);
v___x_2161_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2117_, v_depth_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
return v___x_2161_;
}
}
else
{
lean_dec_ref(v_arg_2117_);
lean_dec(v_depth_2061_);
return v___x_2158_;
}
}
}
}
else
{
lean_object* v_arg_2162_; lean_object* v___x_2163_; 
lean_dec_ref(v___x_2135_);
lean_dec_ref(v___x_2133_);
lean_del_object(v___x_2109_);
lean_dec_ref(v_e_2060_);
v_arg_2162_ = lean_ctor_get(v___x_2123_, 1);
lean_inc_ref(v_arg_2162_);
lean_dec_ref(v___x_2123_);
lean_inc(v_depth_2061_);
v___x_2163_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2162_, v_depth_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; uint8_t v___x_2165_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v___x_2165_ = lean_unbox(v_a_2164_);
if (v___x_2165_ == 0)
{
lean_dec_ref(v_arg_2122_);
lean_dec_ref(v_arg_2117_);
lean_dec(v_depth_2061_);
return v___x_2163_;
}
else
{
lean_object* v___x_2166_; 
lean_dec_ref_known(v___x_2163_, 1);
lean_inc(v_depth_2061_);
v___x_2166_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2122_, v_depth_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; uint8_t v___x_2168_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v___x_2168_ = lean_unbox(v_a_2167_);
if (v___x_2168_ == 0)
{
lean_dec_ref(v_arg_2117_);
lean_dec(v_depth_2061_);
return v___x_2166_;
}
else
{
lean_object* v___x_2169_; 
lean_dec_ref_known(v___x_2166_, 1);
v___x_2169_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2117_, v_depth_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
return v___x_2169_;
}
}
else
{
lean_dec_ref(v_arg_2117_);
lean_dec(v_depth_2061_);
return v___x_2166_;
}
}
}
else
{
lean_dec_ref(v_arg_2122_);
lean_dec_ref(v_arg_2117_);
lean_dec(v_depth_2061_);
return v___x_2163_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2123_);
lean_del_object(v___x_2109_);
lean_dec_ref(v_e_2060_);
v_p_2091_ = v_arg_2122_;
v_q_2092_ = v_arg_2117_;
v___y_2093_ = v_a_2062_;
v___y_2094_ = v_a_2063_;
v___y_2095_ = v_a_2064_;
v___y_2096_ = v_a_2065_;
v___y_2097_ = v_a_2066_;
v___y_2098_ = v_a_2067_;
v___y_2099_ = v_a_2068_;
v___y_2100_ = v_a_2069_;
v___y_2101_ = v_a_2070_;
goto v___jp_2090_;
}
}
else
{
lean_dec_ref(v___x_2123_);
lean_del_object(v___x_2109_);
lean_dec_ref(v_e_2060_);
v_p_2091_ = v_arg_2122_;
v_q_2092_ = v_arg_2117_;
v___y_2093_ = v_a_2062_;
v___y_2094_ = v_a_2063_;
v___y_2095_ = v_a_2064_;
v___y_2096_ = v_a_2065_;
v___y_2097_ = v_a_2066_;
v___y_2098_ = v_a_2067_;
v___y_2099_ = v_a_2068_;
v___y_2100_ = v_a_2069_;
v___y_2101_ = v_a_2070_;
goto v___jp_2090_;
}
}
else
{
lean_dec_ref(v___x_2123_);
lean_del_object(v___x_2109_);
lean_dec_ref(v_e_2060_);
v_p_2091_ = v_arg_2122_;
v_q_2092_ = v_arg_2117_;
v___y_2093_ = v_a_2062_;
v___y_2094_ = v_a_2063_;
v___y_2095_ = v_a_2064_;
v___y_2096_ = v_a_2065_;
v___y_2097_ = v_a_2066_;
v___y_2098_ = v_a_2067_;
v___y_2099_ = v_a_2068_;
v___y_2100_ = v_a_2069_;
v___y_2101_ = v_a_2070_;
goto v___jp_2090_;
}
}
else
{
lean_object* v___x_2170_; 
lean_dec_ref(v___x_2123_);
lean_dec_ref(v_arg_2117_);
lean_del_object(v___x_2109_);
lean_dec_ref(v_e_2060_);
v___x_2170_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_arg_2122_, v_depth_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
return v___x_2170_;
}
}
}
else
{
lean_object* v___x_2171_; 
lean_dec_ref(v___x_2118_);
lean_del_object(v___x_2109_);
lean_dec_ref(v_e_2060_);
v___x_2171_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_arg_2117_, v_depth_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
return v___x_2171_;
}
}
}
else
{
lean_dec_ref(v___x_2111_);
lean_del_object(v___x_2109_);
lean_dec(v_depth_2061_);
lean_dec_ref(v_e_2060_);
goto v___jp_2072_;
}
}
else
{
lean_dec_ref(v___x_2111_);
lean_del_object(v___x_2109_);
lean_dec(v_depth_2061_);
lean_dec_ref(v_e_2060_);
goto v___jp_2072_;
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_depth_2061_);
lean_dec_ref(v_e_2060_);
v_a_2173_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2106_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2106_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
v___jp_2072_:
{
uint8_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = 1;
v___x_2074_ = lean_box(v___x_2073_);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
return v___x_2075_;
}
v___jp_2076_:
{
lean_object* v___x_2086_; 
lean_inc_ref(v_e_2060_);
v___x_2086_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkPredApp(v_e_2060_, v_depth_2061_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v_depth_2061_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; uint8_t v___x_2088_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v___x_2088_ = lean_unbox(v_a_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
lean_dec_ref_known(v___x_2086_, 1);
v___x_2089_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_isBoolAtom___redArg(v_e_2060_, v___y_2082_, v___y_2084_, v___y_2085_);
return v___x_2089_;
}
else
{
lean_dec_ref(v_e_2060_);
return v___x_2086_;
}
}
else
{
lean_dec_ref(v_e_2060_);
return v___x_2086_;
}
}
v___jp_2090_:
{
lean_object* v___x_2102_; 
lean_inc(v_depth_2061_);
v___x_2102_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_p_2091_, v_depth_2061_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; uint8_t v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v___x_2104_ = lean_unbox(v_a_2103_);
if (v___x_2104_ == 0)
{
lean_dec_ref(v_q_2092_);
lean_dec(v_depth_2061_);
return v___x_2102_;
}
else
{
lean_object* v___x_2105_; 
lean_dec_ref_known(v___x_2102_, 1);
v___x_2105_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_q_2092_, v_depth_2061_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
return v___x_2105_;
}
}
else
{
lean_dec_ref(v_q_2092_);
lean_dec(v_depth_2061_);
return v___x_2102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(lean_object* v_e_2181_, lean_object* v_depth_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v___x_2193_; lean_object* v_cache_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; uint8_t v___x_2197_; 
v___x_2193_ = lean_st_ref_get(v_a_2184_);
v_cache_2194_ = lean_ctor_get(v___x_2193_, 1);
lean_inc_ref(v_cache_2194_);
lean_dec(v___x_2193_);
lean_inc(v_depth_2182_);
lean_inc_ref(v_e_2181_);
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v_e_2181_);
lean_ctor_set(v___x_2195_, 1, v_depth_2182_);
v___x_2196_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg(v_cache_2194_, v___x_2195_);
lean_dec_ref(v_cache_2194_);
v___x_2197_ = 1;
if (v___x_2196_ == 0)
{
lean_object* v___x_2198_; 
v___x_2198_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go(v_e_2181_, v_depth_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; uint8_t v___x_2200_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v___x_2200_ = lean_unbox(v_a_2199_);
if (v___x_2200_ == 0)
{
lean_dec_ref_known(v___x_2195_, 2);
return v___x_2198_;
}
else
{
lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2222_; 
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; 
v_unused_2223_ = lean_ctor_get(v___x_2198_, 0);
lean_dec(v_unused_2223_);
v___x_2202_ = v___x_2198_;
v_isShared_2203_ = v_isSharedCheck_2222_;
goto v_resetjp_2201_;
}
else
{
lean_dec(v___x_2198_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2222_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; uint8_t v_mentionsSort_2205_; lean_object* v_usedElements_2206_; lean_object* v_cache_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2221_; 
v___x_2204_ = lean_st_ref_take(v_a_2184_);
v_mentionsSort_2205_ = lean_ctor_get_uint8(v___x_2204_, sizeof(void*)*2);
v_usedElements_2206_ = lean_ctor_get(v___x_2204_, 0);
v_cache_2207_ = lean_ctor_get(v___x_2204_, 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2209_ = v___x_2204_;
v_isShared_2210_ = v_isSharedCheck_2221_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_cache_2207_);
lean_inc(v_usedElements_2206_);
lean_dec(v___x_2204_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2221_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2211_ = lean_box(0);
v___x_2212_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2___redArg(v_cache_2207_, v___x_2195_, v___x_2211_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 1, v___x_2212_);
v___x_2214_ = v___x_2209_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_usedElements_2206_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v___x_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, sizeof(void*)*2, v_mentionsSort_2205_);
v___x_2214_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2215_ = lean_st_ref_put(v_a_2184_, v___x_2214_);
v___x_2216_ = lean_box(v___x_2197_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2216_);
v___x_2218_ = v___x_2202_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2195_, 2);
return v___x_2198_;
}
}
else
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec_ref_known(v___x_2195_, 2);
lean_dec(v_depth_2182_);
lean_dec_ref(v_e_2181_);
v___x_2224_ = lean_box(v___x_2197_);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
return v___x_2225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool___boxed(lean_object* v_e_2226_, lean_object* v_depth_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool(v_e_2226_, v_depth_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp___boxed(lean_object* v_e_2239_, lean_object* v_depth_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_e_2239_, v_depth_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
lean_dec(v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
lean_dec(v_a_2243_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go___boxed(lean_object* v_e_2252_, lean_object* v_depth_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_go(v_e_2252_, v_depth_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
lean_dec(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go___boxed(lean_object* v_e_2265_, lean_object* v_depth_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp_go(v_e_2265_, v_depth_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_);
lean_dec(v_a_2275_);
lean_dec_ref(v_a_2274_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
return v_res_2277_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1(lean_object* v_00_u03b2_2278_, lean_object* v_m_2279_, lean_object* v_a_2280_){
_start:
{
uint8_t v___x_2281_; 
v___x_2281_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___redArg(v_m_2279_, v_a_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1___boxed(lean_object* v_00_u03b2_2282_, lean_object* v_m_2283_, lean_object* v_a_2284_){
_start:
{
uint8_t v_res_2285_; lean_object* v_r_2286_; 
v_res_2285_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1(v_00_u03b2_2282_, v_m_2283_, v_a_2284_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v_m_2283_);
v_r_2286_ = lean_box(v_res_2285_);
return v_r_2286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2(lean_object* v_00_u03b2_2287_, lean_object* v_m_2288_, lean_object* v_a_2289_, lean_object* v_b_2290_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2___redArg(v_m_2288_, v_a_2289_, v_b_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2(lean_object* v_00_u03b2_2292_, lean_object* v_a_2293_, lean_object* v_x_2294_){
_start:
{
uint8_t v___x_2295_; 
v___x_2295_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___redArg(v_a_2293_, v_x_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2296_, lean_object* v_a_2297_, lean_object* v_x_2298_){
_start:
{
uint8_t v_res_2299_; lean_object* v_r_2300_; 
v_res_2299_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__1_spec__2(v_00_u03b2_2296_, v_a_2297_, v_x_2298_);
lean_dec(v_x_2298_);
lean_dec_ref(v_a_2297_);
v_r_2300_ = lean_box(v_res_2299_);
return v_r_2300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4(lean_object* v_00_u03b2_2301_, lean_object* v_data_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4___redArg(v_data_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_2304_, lean_object* v_i_2305_, lean_object* v_source_2306_, lean_object* v_target_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6___redArg(v_i_2305_, v_source_2306_, v_target_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkBool_spec__2_spec__4_spec__6_spec__7___redArg(v_x_2310_, v_x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___redArg(lean_object* v_type_2313_, lean_object* v_acc_2314_, lean_object* v_a_2315_){
_start:
{
if (lean_obj_tag(v_type_2313_) == 7)
{
lean_object* v_binderType_2317_; lean_object* v_body_2318_; lean_object* v___x_2319_; lean_object* v_sortIds_2320_; lean_object* v___x_2321_; 
v_binderType_2317_ = lean_ctor_get(v_type_2313_, 1);
v_body_2318_ = lean_ctor_get(v_type_2313_, 2);
v___x_2319_ = lean_st_ref_get(v_a_2315_);
v_sortIds_2320_ = lean_ctor_get(v___x_2319_, 1);
lean_inc_ref(v_sortIds_2320_);
lean_dec(v___x_2319_);
v___x_2321_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f_go_spec__0___redArg(v_sortIds_2320_, v_binderType_2317_);
lean_dec_ref(v_sortIds_2320_);
if (lean_obj_tag(v___x_2321_) == 1)
{
lean_object* v_val_2322_; lean_object* v___x_2323_; 
lean_inc_ref(v_body_2318_);
lean_dec_ref_known(v_type_2313_, 3);
v_val_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = lean_array_push(v_acc_2314_, v_val_2322_);
v_type_2313_ = v_body_2318_;
v_acc_2314_ = v___x_2323_;
goto _start;
}
else
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec(v___x_2321_);
v___x_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2325_, 0, v_acc_2314_);
lean_ctor_set(v___x_2325_, 1, v_type_2313_);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v_acc_2314_);
lean_ctor_set(v___x_2327_, 1, v_type_2313_);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___redArg___boxed(lean_object* v_type_2329_, lean_object* v_acc_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___redArg(v_type_2329_, v_acc_2330_, v_a_2331_);
lean_dec(v_a_2331_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers(lean_object* v_type_2334_, lean_object* v_acc_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___redArg(v_type_2334_, v_acc_2335_, v_a_2336_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___boxed(lean_object* v_type_2345_, lean_object* v_acc_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers(v_type_2345_, v_acc_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5_spec__8(lean_object* v_msgData_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; lean_object* v_env_2363_; uint8_t v___x_2364_; lean_object* v_env_2365_; lean_object* v___x_2366_; lean_object* v_toCold_2367_; lean_object* v_mctx_2368_; lean_object* v_lctx_2369_; lean_object* v_options_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2362_ = lean_st_ref_get(v___y_2360_);
v_env_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc_ref(v_env_2363_);
lean_dec(v___x_2362_);
v___x_2364_ = 0;
v_env_2365_ = l_Lean_Environment_setRecordingDeps(v_env_2363_, v___x_2364_);
v___x_2366_ = lean_st_ref_get(v___y_2358_);
v_toCold_2367_ = lean_ctor_get(v___y_2359_, 0);
v_mctx_2368_ = lean_ctor_get(v___x_2366_, 0);
lean_inc_ref(v_mctx_2368_);
lean_dec(v___x_2366_);
v_lctx_2369_ = lean_ctor_get(v___y_2357_, 2);
v_options_2370_ = lean_ctor_get(v_toCold_2367_, 2);
lean_inc_ref(v_options_2370_);
lean_inc_ref(v_lctx_2369_);
v___x_2371_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2371_, 0, v_env_2365_);
lean_ctor_set(v___x_2371_, 1, v_mctx_2368_);
lean_ctor_set(v___x_2371_, 2, v_lctx_2369_);
lean_ctor_set(v___x_2371_, 3, v_options_2370_);
v___x_2372_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
lean_ctor_set(v___x_2372_, 1, v_msgData_2356_);
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5_spec__8___boxed(lean_object* v_msgData_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5_spec__8(v_msgData_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
return v_res_2380_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2381_; double v___x_2382_; 
v___x_2381_ = lean_unsigned_to_nat(0u);
v___x_2382_ = lean_float_of_nat(v___x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg(lean_object* v_cls_2386_, lean_object* v_msg_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_ref_2393_; lean_object* v___x_2394_; lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2440_; 
v_ref_2393_ = lean_ctor_get(v___y_2390_, 2);
v___x_2394_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5_spec__8(v_msg_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2440_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2440_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v_traceState_2400_; lean_object* v_env_2401_; lean_object* v_nextMacroScope_2402_; lean_object* v_ngen_2403_; lean_object* v_auxDeclNGen_2404_; lean_object* v_cache_2405_; lean_object* v_recordedDeps_2406_; lean_object* v_messages_2407_; lean_object* v_infoState_2408_; lean_object* v_snapshotTasks_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2439_; 
v___x_2399_ = lean_st_ref_take(v___y_2391_);
v_traceState_2400_ = lean_ctor_get(v___x_2399_, 4);
v_env_2401_ = lean_ctor_get(v___x_2399_, 0);
v_nextMacroScope_2402_ = lean_ctor_get(v___x_2399_, 1);
v_ngen_2403_ = lean_ctor_get(v___x_2399_, 2);
v_auxDeclNGen_2404_ = lean_ctor_get(v___x_2399_, 3);
v_cache_2405_ = lean_ctor_get(v___x_2399_, 5);
v_recordedDeps_2406_ = lean_ctor_get(v___x_2399_, 6);
v_messages_2407_ = lean_ctor_get(v___x_2399_, 7);
v_infoState_2408_ = lean_ctor_get(v___x_2399_, 8);
v_snapshotTasks_2409_ = lean_ctor_get(v___x_2399_, 9);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2411_ = v___x_2399_;
v_isShared_2412_ = v_isSharedCheck_2439_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_snapshotTasks_2409_);
lean_inc(v_infoState_2408_);
lean_inc(v_messages_2407_);
lean_inc(v_recordedDeps_2406_);
lean_inc(v_cache_2405_);
lean_inc(v_traceState_2400_);
lean_inc(v_auxDeclNGen_2404_);
lean_inc(v_ngen_2403_);
lean_inc(v_nextMacroScope_2402_);
lean_inc(v_env_2401_);
lean_dec(v___x_2399_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2439_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
uint64_t v_tid_2413_; lean_object* v_traces_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2438_; 
v_tid_2413_ = lean_ctor_get_uint64(v_traceState_2400_, sizeof(void*)*1);
v_traces_2414_ = lean_ctor_get(v_traceState_2400_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_traceState_2400_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2416_ = v_traceState_2400_;
v_isShared_2417_ = v_isSharedCheck_2438_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_traces_2414_);
lean_dec(v_traceState_2400_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2438_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; double v___x_2420_; uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2418_ = lean_box(0);
v___x_2419_ = lean_box(0);
v___x_2420_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0);
v___x_2421_ = 0;
v___x_2422_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__1));
v___x_2423_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2423_, 0, v_cls_2386_);
lean_ctor_set(v___x_2423_, 1, v___x_2419_);
lean_ctor_set(v___x_2423_, 2, v___x_2422_);
lean_ctor_set_float(v___x_2423_, sizeof(void*)*3, v___x_2420_);
lean_ctor_set_float(v___x_2423_, sizeof(void*)*3 + 8, v___x_2420_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*3 + 16, v___x_2421_);
v___x_2424_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__2));
v___x_2425_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2423_);
lean_ctor_set(v___x_2425_, 1, v_a_2395_);
lean_ctor_set(v___x_2425_, 2, v___x_2424_);
lean_inc(v_ref_2393_);
v___x_2426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2426_, 0, v_ref_2393_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
v___x_2427_ = l_Lean_PersistentArray_push___redArg(v_traces_2414_, v___x_2426_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2427_);
v___x_2429_ = v___x_2416_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2427_);
lean_ctor_set_uint64(v_reuseFailAlloc_2437_, sizeof(void*)*1, v_tid_2413_);
v___x_2429_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2431_; 
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 4, v___x_2429_);
v___x_2431_ = v___x_2411_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_env_2401_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_nextMacroScope_2402_);
lean_ctor_set(v_reuseFailAlloc_2436_, 2, v_ngen_2403_);
lean_ctor_set(v_reuseFailAlloc_2436_, 3, v_auxDeclNGen_2404_);
lean_ctor_set(v_reuseFailAlloc_2436_, 4, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2436_, 5, v_cache_2405_);
lean_ctor_set(v_reuseFailAlloc_2436_, 6, v_recordedDeps_2406_);
lean_ctor_set(v_reuseFailAlloc_2436_, 7, v_messages_2407_);
lean_ctor_set(v_reuseFailAlloc_2436_, 8, v_infoState_2408_);
lean_ctor_set(v_reuseFailAlloc_2436_, 9, v_snapshotTasks_2409_);
v___x_2431_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2434_; 
v___x_2432_ = lean_st_ref_put(v___y_2391_, v___x_2431_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2418_);
v___x_2434_ = v___x_2397_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2418_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___boxed(lean_object* v_cls_2441_, lean_object* v_msg_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg(v_cls_2441_, v_msg_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0(lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
if (lean_obj_tag(v_a_2449_) == 0)
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2451_, 0, v_a_2450_);
return v___x_2451_;
}
else
{
lean_object* v_key_2452_; lean_object* v_value_2453_; lean_object* v_tail_2454_; lean_object* v_r_2455_; 
v_key_2452_ = lean_ctor_get(v_a_2449_, 0);
lean_inc(v_key_2452_);
v_value_2453_ = lean_ctor_get(v_a_2449_, 1);
lean_inc(v_value_2453_);
v_tail_2454_ = lean_ctor_get(v_a_2449_, 2);
lean_inc(v_tail_2454_);
lean_dec_ref_known(v_a_2449_, 3);
v_r_2455_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkTerm_spec__0___redArg(v_a_2450_, v_key_2452_, v_value_2453_);
v_a_2449_ = v_tail_2454_;
v_a_2450_ = v_r_2455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2(lean_object* v_as_2457_, size_t v_sz_2458_, size_t v_i_2459_, lean_object* v_b_2460_){
_start:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_usize_dec_lt(v_i_2459_, v_sz_2458_);
if (v___x_2461_ == 0)
{
return v_b_2460_;
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2463_; 
v_a_2462_ = lean_array_uget_borrowed(v_as_2457_, v_i_2459_);
lean_inc(v_a_2462_);
v___x_2463_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__0(v_a_2462_, v_b_2460_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 1);
return v_a_2464_;
}
else
{
lean_object* v_a_2465_; size_t v___x_2466_; size_t v___x_2467_; 
v_a_2465_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___x_2463_, 1);
v___x_2466_ = ((size_t)1ULL);
v___x_2467_ = lean_usize_add(v_i_2459_, v___x_2466_);
v_i_2459_ = v___x_2467_;
v_b_2460_ = v_a_2465_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2___boxed(lean_object* v_as_2469_, lean_object* v_sz_2470_, lean_object* v_i_2471_, lean_object* v_b_2472_){
_start:
{
size_t v_sz_boxed_2473_; size_t v_i_boxed_2474_; lean_object* v_res_2475_; 
v_sz_boxed_2473_ = lean_unbox_usize(v_sz_2470_);
lean_dec(v_sz_2470_);
v_i_boxed_2474_ = lean_unbox_usize(v_i_2471_);
lean_dec(v_i_2471_);
v_res_2475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2(v_as_2469_, v_sz_boxed_2473_, v_i_boxed_2474_, v_b_2472_);
lean_dec_ref(v_as_2469_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5_spec__6(lean_object* v_msg_2476_){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default;
v___x_2478_ = lean_panic_fn_borrowed(v___x_2477_, v_msg_2476_);
return v___x_2478_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2482_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__2));
v___x_2483_ = lean_unsigned_to_nat(11u);
v___x_2484_ = lean_unsigned_to_nat(163u);
v___x_2485_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__1));
v___x_2486_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__0));
v___x_2487_ = l_mkPanicMessageWithDecl(v___x_2486_, v___x_2485_, v___x_2484_, v___x_2483_, v___x_2482_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5(lean_object* v_a_2488_, lean_object* v_x_2489_){
_start:
{
if (lean_obj_tag(v_x_2489_) == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__3);
v___x_2491_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5_spec__6(v___x_2490_);
return v___x_2491_;
}
else
{
lean_object* v_key_2492_; lean_object* v_value_2493_; lean_object* v_tail_2494_; uint8_t v___x_2495_; 
v_key_2492_ = lean_ctor_get(v_x_2489_, 0);
v_value_2493_ = lean_ctor_get(v_x_2489_, 1);
v_tail_2494_ = lean_ctor_get(v_x_2489_, 2);
v___x_2495_ = lean_nat_dec_eq(v_key_2492_, v_a_2488_);
if (v___x_2495_ == 0)
{
v_x_2489_ = v_tail_2494_;
goto _start;
}
else
{
lean_inc(v_value_2493_);
return v_value_2493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___boxed(lean_object* v_a_2497_, lean_object* v_x_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5(v_a_2497_, v_x_2498_);
lean_dec(v_x_2498_);
lean_dec(v_a_2497_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3(lean_object* v_m_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v_buckets_2502_; lean_object* v___x_2503_; uint64_t v___x_2504_; uint64_t v___x_2505_; uint64_t v___x_2506_; uint64_t v_fold_2507_; uint64_t v___x_2508_; uint64_t v___x_2509_; uint64_t v___x_2510_; size_t v___x_2511_; size_t v___x_2512_; size_t v___x_2513_; size_t v___x_2514_; size_t v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v_buckets_2502_ = lean_ctor_get(v_m_2500_, 1);
v___x_2503_ = lean_array_get_size(v_buckets_2502_);
v___x_2504_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_a_2501_);
v___x_2505_ = 32ULL;
v___x_2506_ = lean_uint64_shift_right(v___x_2504_, v___x_2505_);
v_fold_2507_ = lean_uint64_xor(v___x_2504_, v___x_2506_);
v___x_2508_ = 16ULL;
v___x_2509_ = lean_uint64_shift_right(v_fold_2507_, v___x_2508_);
v___x_2510_ = lean_uint64_xor(v_fold_2507_, v___x_2509_);
v___x_2511_ = lean_uint64_to_usize(v___x_2510_);
v___x_2512_ = lean_usize_of_nat(v___x_2503_);
v___x_2513_ = ((size_t)1ULL);
v___x_2514_ = lean_usize_sub(v___x_2512_, v___x_2513_);
v___x_2515_ = lean_usize_land(v___x_2511_, v___x_2514_);
v___x_2516_ = lean_array_uget_borrowed(v_buckets_2502_, v___x_2515_);
v___x_2517_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5(v_a_2501_, v___x_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3___boxed(lean_object* v_m_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3(v_m_2518_, v_a_2519_);
lean_dec(v_a_2519_);
lean_dec_ref(v_m_2518_);
return v_res_2520_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__4(lean_object* v___x_2521_, lean_object* v_as_2522_, size_t v_i_2523_, size_t v_stop_2524_){
_start:
{
uint8_t v___x_2525_; 
v___x_2525_ = lean_usize_dec_eq(v_i_2523_, v_stop_2524_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v_elements_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2526_ = lean_array_uget_borrowed(v_as_2522_, v_i_2523_);
v___x_2527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3(v___x_2521_, v___x_2526_);
v_elements_2528_ = lean_ctor_get(v___x_2527_, 2);
lean_inc_ref(v_elements_2528_);
lean_dec_ref(v___x_2527_);
v___x_2529_ = lean_array_get_size(v_elements_2528_);
lean_dec_ref(v_elements_2528_);
v___x_2530_ = lean_unsigned_to_nat(0u);
v___x_2531_ = lean_nat_dec_eq(v___x_2529_, v___x_2530_);
if (v___x_2531_ == 0)
{
size_t v___x_2532_; size_t v___x_2533_; 
v___x_2532_ = ((size_t)1ULL);
v___x_2533_ = lean_usize_add(v_i_2523_, v___x_2532_);
v_i_2523_ = v___x_2533_;
goto _start;
}
else
{
return v___x_2531_;
}
}
else
{
uint8_t v___x_2535_; 
v___x_2535_ = 0;
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__4___boxed(lean_object* v___x_2536_, lean_object* v_as_2537_, lean_object* v_i_2538_, lean_object* v_stop_2539_){
_start:
{
size_t v_i_boxed_2540_; size_t v_stop_boxed_2541_; uint8_t v_res_2542_; lean_object* v_r_2543_; 
v_i_boxed_2540_ = lean_unbox_usize(v_i_2538_);
lean_dec(v_i_2538_);
v_stop_boxed_2541_ = lean_unbox_usize(v_stop_2539_);
lean_dec(v_stop_2539_);
v_res_2542_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__4(v___x_2536_, v_as_2537_, v_i_boxed_2540_, v_stop_boxed_2541_);
lean_dec_ref(v_as_2537_);
lean_dec_ref(v___x_2536_);
v_r_2543_ = lean_box(v_res_2542_);
return v_r_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1_spec__1(lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
if (lean_obj_tag(v_a_2544_) == 0)
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2546_, 0, v_a_2545_);
return v___x_2546_;
}
else
{
lean_object* v_key_2547_; lean_object* v_value_2548_; lean_object* v_tail_2549_; lean_object* v_r_2550_; 
v_key_2547_ = lean_ctor_get(v_a_2544_, 0);
lean_inc(v_key_2547_);
v_value_2548_ = lean_ctor_get(v_a_2544_, 1);
lean_inc(v_value_2548_);
v_tail_2549_ = lean_ctor_get(v_a_2544_, 2);
lean_inc(v_tail_2549_);
lean_dec_ref_known(v_a_2544_, 3);
v_r_2550_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1___redArg(v_a_2545_, v_key_2547_, v_value_2548_);
v_a_2544_ = v_tail_2549_;
v_a_2545_ = v_r_2550_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1_spec__2(lean_object* v_as_2552_, size_t v_sz_2553_, size_t v_i_2554_, lean_object* v_b_2555_){
_start:
{
uint8_t v___x_2556_; 
v___x_2556_ = lean_usize_dec_lt(v_i_2554_, v_sz_2553_);
if (v___x_2556_ == 0)
{
return v_b_2555_;
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2558_; 
v_a_2557_ = lean_array_uget_borrowed(v_as_2552_, v_i_2554_);
lean_inc(v_a_2557_);
v___x_2558_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1_spec__1(v_a_2557_, v_b_2555_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
return v_a_2559_;
}
else
{
lean_object* v_a_2560_; size_t v___x_2561_; size_t v___x_2562_; 
v_a_2560_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2561_ = ((size_t)1ULL);
v___x_2562_ = lean_usize_add(v_i_2554_, v___x_2561_);
v_i_2554_ = v___x_2562_;
v_b_2555_ = v_a_2560_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1_spec__2___boxed(lean_object* v_as_2564_, lean_object* v_sz_2565_, lean_object* v_i_2566_, lean_object* v_b_2567_){
_start:
{
size_t v_sz_boxed_2568_; size_t v_i_boxed_2569_; lean_object* v_res_2570_; 
v_sz_boxed_2568_ = lean_unbox_usize(v_sz_2565_);
lean_dec(v_sz_2565_);
v_i_boxed_2569_ = lean_unbox_usize(v_i_2566_);
lean_dec(v_i_2566_);
v_res_2570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1_spec__2(v_as_2564_, v_sz_boxed_2568_, v_i_boxed_2569_, v_b_2567_);
lean_dec_ref(v_as_2564_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1(lean_object* v_m_2571_, lean_object* v_l_2572_){
_start:
{
lean_object* v_buckets_2573_; size_t v_sz_2574_; size_t v___x_2575_; lean_object* v___x_2576_; 
v_buckets_2573_ = lean_ctor_get(v_l_2572_, 1);
v_sz_2574_ = lean_array_size(v_buckets_2573_);
v___x_2575_ = ((size_t)0ULL);
v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1_spec__2(v_buckets_2573_, v_sz_2574_, v___x_2575_, v_m_2571_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1___boxed(lean_object* v_m_2577_, lean_object* v_l_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1(v_m_2577_, v_l_2578_);
lean_dec_ref(v_l_2578_);
return v_res_2579_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__0(void){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = lean_box(0);
v___x_2581_ = lean_unsigned_to_nat(16u);
v___x_2582_ = lean_mk_array(v___x_2581_, v___x_2580_);
return v___x_2582_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__1(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__0);
v___x_2584_ = lean_unsigned_to_nat(0u);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set(v___x_2585_, 1, v___x_2583_);
return v___x_2585_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_2599_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__8));
v___x_2600_ = l_Lean_Name_append(v___x_2599_, v___x_2598_);
return v___x_2600_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__11(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__10));
v___x_2603_ = l_Lean_stringToMessageData(v___x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f(lean_object* v_hyp_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_type_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2718_; 
v_type_2619_ = lean_ctor_get(v_hyp_2604_, 1);
lean_inc_ref_n(v_type_2619_, 2);
lean_dec_ref(v_hyp_2604_);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_predType_x3f___redArg___closed__0));
v___x_2622_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_stripQuantifiers___redArg(v_type_2619_, v___x_2621_, v_a_2605_);
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2718_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2718_;
goto v_resetjp_2624_;
}
v___jp_2613_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = lean_box(0);
v___x_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
return v___x_2615_;
}
v___jp_2616_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = lean_box(0);
v___x_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
return v___x_2618_;
}
v_resetjp_2624_:
{
lean_object* v_fst_2627_; lean_object* v_snd_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2717_; 
v_fst_2627_ = lean_ctor_get(v_a_2623_, 0);
v_snd_2628_ = lean_ctor_get(v_a_2623_, 1);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_a_2623_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2630_ = v_a_2623_;
v_isShared_2631_ = v_isSharedCheck_2717_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_snd_2628_);
lean_inc(v_fst_2627_);
lean_dec(v_a_2623_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2717_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2649_; lean_object* v___x_2668_; uint8_t v___y_2670_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2668_ = lean_st_ref_get(v_a_2605_);
v___x_2690_ = lean_array_get_size(v_fst_2627_);
v___x_2691_ = lean_nat_dec_lt(v___x_2620_, v___x_2690_);
if (v___x_2691_ == 0)
{
lean_dec(v___x_2668_);
lean_del_object(v___x_2630_);
lean_dec_ref(v_type_2619_);
v___y_2670_ = v___x_2691_;
goto v___jp_2669_;
}
else
{
if (v___x_2691_ == 0)
{
lean_dec(v___x_2668_);
lean_del_object(v___x_2630_);
lean_dec_ref(v_type_2619_);
v___y_2670_ = v___x_2691_;
goto v___jp_2669_;
}
else
{
lean_object* v_sorts_2692_; size_t v___x_2693_; size_t v___x_2694_; uint8_t v___x_2695_; 
v_sorts_2692_ = lean_ctor_get(v___x_2668_, 0);
lean_inc_ref(v_sorts_2692_);
lean_dec(v___x_2668_);
v___x_2693_ = ((size_t)0ULL);
v___x_2694_ = lean_usize_of_nat(v___x_2690_);
v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__4(v_sorts_2692_, v_fst_2627_, v___x_2693_, v___x_2694_);
lean_dec_ref(v_sorts_2692_);
if (v___x_2695_ == 0)
{
lean_del_object(v___x_2630_);
lean_dec_ref(v_type_2619_);
v___y_2670_ = v___x_2695_;
goto v___jp_2669_;
}
else
{
lean_object* v_toCold_2696_; lean_object* v_options_2697_; uint8_t v_hasTrace_2698_; 
lean_dec(v_snd_2628_);
lean_dec(v_fst_2627_);
lean_del_object(v___x_2625_);
v_toCold_2696_ = lean_ctor_get(v_a_2610_, 0);
v_options_2697_ = lean_ctor_get(v_toCold_2696_, 2);
v_hasTrace_2698_ = lean_ctor_get_uint8(v_options_2697_, sizeof(void*)*1);
if (v_hasTrace_2698_ == 0)
{
lean_del_object(v___x_2630_);
lean_dec_ref(v_type_2619_);
goto v___jp_2613_;
}
else
{
lean_object* v_inheritedTraceOptions_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v_inheritedTraceOptions_2699_ = lean_ctor_get(v_toCold_2696_, 11);
v___x_2700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_2701_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9);
v___x_2702_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2699_, v_options_2697_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_del_object(v___x_2630_);
lean_dec_ref(v_type_2619_);
goto v___jp_2613_;
}
else
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__11, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__11_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__11);
v___x_2704_ = l_Lean_MessageData_ofExpr(v_type_2619_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set_tag(v___x_2630_, 7);
lean_ctor_set(v___x_2630_, 1, v___x_2704_);
lean_ctor_set(v___x_2630_, 0, v___x_2703_);
v___x_2706_ = v___x_2630_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg(v___x_2700_, v___x_2706_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_dec_ref_known(v___x_2707_, 1);
goto v___jp_2613_;
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
}
}
}
}
v___jp_2632_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2642_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2642_, 0, v___y_2634_);
lean_ctor_set(v___x_2642_, 1, v___y_2635_);
lean_ctor_set(v___x_2642_, 2, v___y_2637_);
lean_ctor_set(v___x_2642_, 3, v___y_2640_);
lean_ctor_set(v___x_2642_, 4, v___y_2638_);
lean_ctor_set(v___x_2642_, 5, v___y_2641_);
lean_ctor_set(v___x_2642_, 6, v___y_2633_);
lean_ctor_set(v___x_2642_, 7, v___y_2639_);
lean_ctor_set(v___x_2642_, 8, v___y_2636_);
v___x_2643_ = lean_st_ref_put(v_a_2605_, v___x_2642_);
v___x_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2644_, 0, v_fst_2627_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2644_);
v___x_2646_ = v___x_2625_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
v___jp_2648_:
{
lean_object* v___x_2650_; lean_object* v_usedElements_2651_; lean_object* v_sorts_2652_; lean_object* v_sortIds_2653_; lean_object* v_nextSortId_2654_; lean_object* v_elements_2655_; lean_object* v_preds_2656_; lean_object* v_groundFacts_2657_; lean_object* v_quantifiedFacts_2658_; lean_object* v_remainingHyps_2659_; lean_object* v_size_2660_; lean_object* v_buckets_2661_; lean_object* v_size_2662_; uint8_t v___x_2663_; 
v___x_2650_ = lean_st_ref_take(v_a_2605_);
v_usedElements_2651_ = lean_ctor_get(v___x_2650_, 5);
lean_inc_ref(v_usedElements_2651_);
v_sorts_2652_ = lean_ctor_get(v___x_2650_, 0);
lean_inc_ref(v_sorts_2652_);
v_sortIds_2653_ = lean_ctor_get(v___x_2650_, 1);
lean_inc_ref(v_sortIds_2653_);
v_nextSortId_2654_ = lean_ctor_get(v___x_2650_, 2);
lean_inc(v_nextSortId_2654_);
v_elements_2655_ = lean_ctor_get(v___x_2650_, 3);
lean_inc_ref(v_elements_2655_);
v_preds_2656_ = lean_ctor_get(v___x_2650_, 4);
lean_inc_ref(v_preds_2656_);
v_groundFacts_2657_ = lean_ctor_get(v___x_2650_, 6);
lean_inc_ref(v_groundFacts_2657_);
v_quantifiedFacts_2658_ = lean_ctor_get(v___x_2650_, 7);
lean_inc_ref(v_quantifiedFacts_2658_);
v_remainingHyps_2659_ = lean_ctor_get(v___x_2650_, 8);
lean_inc_ref(v_remainingHyps_2659_);
lean_dec(v___x_2650_);
v_size_2660_ = lean_ctor_get(v_usedElements_2651_, 0);
v_buckets_2661_ = lean_ctor_get(v_usedElements_2651_, 1);
v_size_2662_ = lean_ctor_get(v___y_2649_, 0);
v___x_2663_ = lean_nat_dec_le(v_size_2660_, v_size_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__1(v_usedElements_2651_, v___y_2649_);
lean_dec_ref(v___y_2649_);
v___y_2633_ = v_groundFacts_2657_;
v___y_2634_ = v_sorts_2652_;
v___y_2635_ = v_sortIds_2653_;
v___y_2636_ = v_remainingHyps_2659_;
v___y_2637_ = v_nextSortId_2654_;
v___y_2638_ = v_preds_2656_;
v___y_2639_ = v_quantifiedFacts_2658_;
v___y_2640_ = v_elements_2655_;
v___y_2641_ = v___x_2664_;
goto v___jp_2632_;
}
else
{
size_t v_sz_2665_; size_t v___x_2666_; lean_object* v___x_2667_; 
lean_inc_ref(v_buckets_2661_);
lean_dec_ref(v_usedElements_2651_);
v_sz_2665_ = lean_array_size(v_buckets_2661_);
v___x_2666_ = ((size_t)0ULL);
v___x_2667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__2(v_buckets_2661_, v_sz_2665_, v___x_2666_, v___y_2649_);
lean_dec_ref(v_buckets_2661_);
v___y_2633_ = v_groundFacts_2657_;
v___y_2634_ = v_sorts_2652_;
v___y_2635_ = v_sortIds_2653_;
v___y_2636_ = v_remainingHyps_2659_;
v___y_2637_ = v_nextSortId_2654_;
v___y_2638_ = v_preds_2656_;
v___y_2639_ = v_quantifiedFacts_2658_;
v___y_2640_ = v_elements_2655_;
v___y_2641_ = v___x_2667_;
goto v___jp_2632_;
}
}
v___jp_2669_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2671_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__1);
v___x_2672_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*2, v___y_2670_);
v___x_2673_ = lean_st_mk_ref(v___x_2672_);
v___x_2674_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ScanM_checkProp(v_snd_2628_, v___x_2620_, v_fst_2627_, v___x_2673_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2674_, 1);
v___x_2676_ = lean_st_ref_get(v___x_2673_);
lean_dec(v___x_2673_);
v___x_2677_ = lean_unbox(v_a_2675_);
lean_dec(v_a_2675_);
if (v___x_2677_ == 0)
{
lean_dec(v___x_2676_);
lean_dec(v_fst_2627_);
lean_del_object(v___x_2625_);
goto v___jp_2616_;
}
else
{
if (v___y_2670_ == 0)
{
uint8_t v_mentionsSort_2678_; lean_object* v_usedElements_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; 
v_mentionsSort_2678_ = lean_ctor_get_uint8(v___x_2676_, sizeof(void*)*2);
v_usedElements_2679_ = lean_ctor_get(v___x_2676_, 0);
lean_inc_ref(v_usedElements_2679_);
lean_dec(v___x_2676_);
v___x_2680_ = lean_array_get_size(v_fst_2627_);
v___x_2681_ = lean_nat_dec_eq(v___x_2680_, v___x_2620_);
if (v___x_2681_ == 0)
{
v___y_2649_ = v_usedElements_2679_;
goto v___jp_2648_;
}
else
{
if (v_mentionsSort_2678_ == 0)
{
lean_dec_ref(v_usedElements_2679_);
lean_dec(v_fst_2627_);
lean_del_object(v___x_2625_);
goto v___jp_2616_;
}
else
{
v___y_2649_ = v_usedElements_2679_;
goto v___jp_2648_;
}
}
}
else
{
lean_dec(v___x_2676_);
lean_dec(v_fst_2627_);
lean_del_object(v___x_2625_);
goto v___jp_2616_;
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v___x_2673_);
lean_dec(v_fst_2627_);
lean_del_object(v___x_2625_);
v_a_2682_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2674_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2674_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___boxed(lean_object* v_hyp_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f(v_hyp_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
lean_dec(v_a_2726_);
lean_dec_ref(v_a_2725_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
lean_dec(v_a_2720_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5(lean_object* v_cls_2729_, lean_object* v_msg_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg(v_cls_2729_, v_msg_2730_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___boxed(lean_object* v_cls_2740_, lean_object* v_msg_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5(v_cls_2740_, v_msg_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processHyp(lean_object* v_hyp_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v___x_2760_; 
lean_inc_ref(v_hyp_2751_);
v___x_2760_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f(v_hyp_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2839_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2763_ = v___x_2760_;
v_isShared_2764_ = v_isSharedCheck_2839_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2760_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2839_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
if (lean_obj_tag(v_a_2761_) == 0)
{
lean_object* v___x_2765_; lean_object* v_sorts_2766_; lean_object* v_sortIds_2767_; lean_object* v_nextSortId_2768_; lean_object* v_elements_2769_; lean_object* v_preds_2770_; lean_object* v_usedElements_2771_; lean_object* v_groundFacts_2772_; lean_object* v_quantifiedFacts_2773_; lean_object* v_remainingHyps_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2787_; 
v___x_2765_ = lean_st_ref_take(v_a_2752_);
v_sorts_2766_ = lean_ctor_get(v___x_2765_, 0);
v_sortIds_2767_ = lean_ctor_get(v___x_2765_, 1);
v_nextSortId_2768_ = lean_ctor_get(v___x_2765_, 2);
v_elements_2769_ = lean_ctor_get(v___x_2765_, 3);
v_preds_2770_ = lean_ctor_get(v___x_2765_, 4);
v_usedElements_2771_ = lean_ctor_get(v___x_2765_, 5);
v_groundFacts_2772_ = lean_ctor_get(v___x_2765_, 6);
v_quantifiedFacts_2773_ = lean_ctor_get(v___x_2765_, 7);
v_remainingHyps_2774_ = lean_ctor_get(v___x_2765_, 8);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2776_ = v___x_2765_;
v_isShared_2777_ = v_isSharedCheck_2787_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_remainingHyps_2774_);
lean_inc(v_quantifiedFacts_2773_);
lean_inc(v_groundFacts_2772_);
lean_inc(v_usedElements_2771_);
lean_inc(v_preds_2770_);
lean_inc(v_elements_2769_);
lean_inc(v_nextSortId_2768_);
lean_inc(v_sortIds_2767_);
lean_inc(v_sorts_2766_);
lean_dec(v___x_2765_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2787_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2778_ = lean_box(0);
v___x_2779_ = lean_array_push(v_remainingHyps_2774_, v_hyp_2751_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 8, v___x_2779_);
v___x_2781_ = v___x_2776_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_sorts_2766_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_sortIds_2767_);
lean_ctor_set(v_reuseFailAlloc_2786_, 2, v_nextSortId_2768_);
lean_ctor_set(v_reuseFailAlloc_2786_, 3, v_elements_2769_);
lean_ctor_set(v_reuseFailAlloc_2786_, 4, v_preds_2770_);
lean_ctor_set(v_reuseFailAlloc_2786_, 5, v_usedElements_2771_);
lean_ctor_set(v_reuseFailAlloc_2786_, 6, v_groundFacts_2772_);
lean_ctor_set(v_reuseFailAlloc_2786_, 7, v_quantifiedFacts_2773_);
lean_ctor_set(v_reuseFailAlloc_2786_, 8, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2782_ = lean_st_ref_put(v_a_2752_, v___x_2781_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v___x_2778_);
v___x_2784_ = v___x_2763_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2778_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
else
{
lean_object* v_val_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v_val_2788_ = lean_ctor_get(v_a_2761_, 0);
lean_inc(v_val_2788_);
lean_dec_ref_known(v_a_2761_, 1);
v___x_2789_ = lean_array_get_size(v_val_2788_);
v___x_2790_ = lean_unsigned_to_nat(0u);
v___x_2791_ = lean_nat_dec_eq(v___x_2789_, v___x_2790_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; lean_object* v_sorts_2793_; lean_object* v_sortIds_2794_; lean_object* v_nextSortId_2795_; lean_object* v_elements_2796_; lean_object* v_preds_2797_; lean_object* v_usedElements_2798_; lean_object* v_groundFacts_2799_; lean_object* v_quantifiedFacts_2800_; lean_object* v_remainingHyps_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2815_; 
v___x_2792_ = lean_st_ref_take(v_a_2752_);
v_sorts_2793_ = lean_ctor_get(v___x_2792_, 0);
v_sortIds_2794_ = lean_ctor_get(v___x_2792_, 1);
v_nextSortId_2795_ = lean_ctor_get(v___x_2792_, 2);
v_elements_2796_ = lean_ctor_get(v___x_2792_, 3);
v_preds_2797_ = lean_ctor_get(v___x_2792_, 4);
v_usedElements_2798_ = lean_ctor_get(v___x_2792_, 5);
v_groundFacts_2799_ = lean_ctor_get(v___x_2792_, 6);
v_quantifiedFacts_2800_ = lean_ctor_get(v___x_2792_, 7);
v_remainingHyps_2801_ = lean_ctor_get(v___x_2792_, 8);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2803_ = v___x_2792_;
v_isShared_2804_ = v_isSharedCheck_2815_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_remainingHyps_2801_);
lean_inc(v_quantifiedFacts_2800_);
lean_inc(v_groundFacts_2799_);
lean_inc(v_usedElements_2798_);
lean_inc(v_preds_2797_);
lean_inc(v_elements_2796_);
lean_inc(v_nextSortId_2795_);
lean_inc(v_sortIds_2794_);
lean_inc(v_sorts_2793_);
lean_dec(v___x_2792_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2815_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2809_; 
v___x_2805_ = lean_box(0);
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v_hyp_2751_);
lean_ctor_set(v___x_2806_, 1, v_val_2788_);
v___x_2807_ = lean_array_push(v_quantifiedFacts_2800_, v___x_2806_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 7, v___x_2807_);
v___x_2809_ = v___x_2803_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_sorts_2793_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_sortIds_2794_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v_nextSortId_2795_);
lean_ctor_set(v_reuseFailAlloc_2814_, 3, v_elements_2796_);
lean_ctor_set(v_reuseFailAlloc_2814_, 4, v_preds_2797_);
lean_ctor_set(v_reuseFailAlloc_2814_, 5, v_usedElements_2798_);
lean_ctor_set(v_reuseFailAlloc_2814_, 6, v_groundFacts_2799_);
lean_ctor_set(v_reuseFailAlloc_2814_, 7, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2814_, 8, v_remainingHyps_2801_);
v___x_2809_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2810_ = lean_st_ref_put(v_a_2752_, v___x_2809_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v___x_2805_);
v___x_2812_ = v___x_2763_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2805_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
else
{
lean_object* v___x_2816_; lean_object* v_sorts_2817_; lean_object* v_sortIds_2818_; lean_object* v_nextSortId_2819_; lean_object* v_elements_2820_; lean_object* v_preds_2821_; lean_object* v_usedElements_2822_; lean_object* v_groundFacts_2823_; lean_object* v_quantifiedFacts_2824_; lean_object* v_remainingHyps_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2838_; 
lean_dec(v_val_2788_);
v___x_2816_ = lean_st_ref_take(v_a_2752_);
v_sorts_2817_ = lean_ctor_get(v___x_2816_, 0);
v_sortIds_2818_ = lean_ctor_get(v___x_2816_, 1);
v_nextSortId_2819_ = lean_ctor_get(v___x_2816_, 2);
v_elements_2820_ = lean_ctor_get(v___x_2816_, 3);
v_preds_2821_ = lean_ctor_get(v___x_2816_, 4);
v_usedElements_2822_ = lean_ctor_get(v___x_2816_, 5);
v_groundFacts_2823_ = lean_ctor_get(v___x_2816_, 6);
v_quantifiedFacts_2824_ = lean_ctor_get(v___x_2816_, 7);
v_remainingHyps_2825_ = lean_ctor_get(v___x_2816_, 8);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2827_ = v___x_2816_;
v_isShared_2828_ = v_isSharedCheck_2838_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_remainingHyps_2825_);
lean_inc(v_quantifiedFacts_2824_);
lean_inc(v_groundFacts_2823_);
lean_inc(v_usedElements_2822_);
lean_inc(v_preds_2821_);
lean_inc(v_elements_2820_);
lean_inc(v_nextSortId_2819_);
lean_inc(v_sortIds_2818_);
lean_inc(v_sorts_2817_);
lean_dec(v___x_2816_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2838_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2832_; 
v___x_2829_ = lean_box(0);
v___x_2830_ = lean_array_push(v_groundFacts_2823_, v_hyp_2751_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 6, v___x_2830_);
v___x_2832_ = v___x_2827_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_sorts_2817_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_sortIds_2818_);
lean_ctor_set(v_reuseFailAlloc_2837_, 2, v_nextSortId_2819_);
lean_ctor_set(v_reuseFailAlloc_2837_, 3, v_elements_2820_);
lean_ctor_set(v_reuseFailAlloc_2837_, 4, v_preds_2821_);
lean_ctor_set(v_reuseFailAlloc_2837_, 5, v_usedElements_2822_);
lean_ctor_set(v_reuseFailAlloc_2837_, 6, v___x_2830_);
lean_ctor_set(v_reuseFailAlloc_2837_, 7, v_quantifiedFacts_2824_);
lean_ctor_set(v_reuseFailAlloc_2837_, 8, v_remainingHyps_2825_);
v___x_2832_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2833_ = lean_st_ref_put(v_a_2752_, v___x_2832_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v___x_2829_);
v___x_2835_ = v___x_2763_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2829_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec_ref(v_hyp_2751_);
v_a_2840_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2760_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2760_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processHyp___boxed(lean_object* v_hyp_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processHyp(v_hyp_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0(lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
if (lean_obj_tag(v_a_2866_) == 0)
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2876_, 0, v_a_2867_);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
else
{
lean_object* v_value_2878_; lean_object* v_key_2879_; lean_object* v_tail_2880_; lean_object* v_type_2881_; lean_object* v_level_2882_; lean_object* v_elements_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; 
v_value_2878_ = lean_ctor_get(v_a_2866_, 1);
lean_inc(v_value_2878_);
v_key_2879_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_key_2879_);
v_tail_2880_ = lean_ctor_get(v_a_2866_, 2);
lean_inc(v_tail_2880_);
lean_dec_ref_known(v_a_2866_, 3);
v_type_2881_ = lean_ctor_get(v_value_2878_, 0);
lean_inc_ref(v_type_2881_);
v_level_2882_ = lean_ctor_get(v_value_2878_, 1);
lean_inc(v_level_2882_);
v_elements_2883_ = lean_ctor_get(v_value_2878_, 2);
lean_inc_ref(v_elements_2883_);
lean_dec(v_value_2878_);
v___x_2884_ = lean_box(0);
v___x_2885_ = lean_array_get_size(v_elements_2883_);
lean_dec_ref(v_elements_2883_);
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = lean_nat_dec_eq(v___x_2885_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_dec(v_level_2882_);
lean_dec_ref(v_type_2881_);
lean_dec(v_key_2879_);
v_a_2866_ = v_tail_2880_;
v_a_2867_ = v___x_2884_;
goto _start;
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2889_ = l_Lean_Level_succ___override(v_level_2882_);
v___x_2890_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__1));
v___x_2891_ = lean_box(0);
v___x_2892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2889_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
lean_inc_ref(v___x_2892_);
v___x_2893_ = l_Lean_mkConst(v___x_2890_, v___x_2892_);
lean_inc_ref(v_type_2881_);
v___x_2894_ = l_Lean_Expr_app___override(v___x_2893_, v_type_2881_);
v___x_2895_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2894_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2897_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___x_2895_, 1);
v___x_2897_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_2896_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref_known(v___x_2897_, 1);
if (lean_obj_tag(v_a_2898_) == 1)
{
lean_object* v_val_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_val_2899_ = lean_ctor_get(v_a_2898_, 0);
lean_inc(v_val_2899_);
lean_dec_ref_known(v_a_2898_, 1);
v___x_2900_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___closed__4));
v___x_2901_ = l_Lean_mkConst(v___x_2900_, v___x_2892_);
v___x_2902_ = l_Lean_mkAppB(v___x_2901_, v_type_2881_, v_val_2899_);
v___x_2903_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2902_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerElement___redArg(v_a_2904_, v_key_2879_, v___y_2868_);
lean_dec_ref(v___x_2905_);
v_a_2866_ = v_tail_2880_;
v_a_2867_ = v___x_2884_;
goto _start;
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec(v_tail_2880_);
lean_dec(v_key_2879_);
v_a_2907_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2903_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2903_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
lean_dec(v_a_2898_);
lean_dec_ref_known(v___x_2892_, 2);
lean_dec_ref(v_type_2881_);
lean_dec(v_key_2879_);
v_a_2866_ = v_tail_2880_;
v_a_2867_ = v___x_2884_;
goto _start;
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref_known(v___x_2892_, 2);
lean_dec_ref(v_type_2881_);
lean_dec(v_tail_2880_);
lean_dec(v_key_2879_);
v_a_2916_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2897_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2897_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec_ref_known(v___x_2892_, 2);
lean_dec_ref(v_type_2881_);
lean_dec(v_tail_2880_);
lean_dec(v_key_2879_);
v_a_2924_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2895_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2895_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0___boxed(lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0(v_a_2932_, v_a_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__1(lean_object* v_as_2943_, size_t v_sz_2944_, size_t v_i_2945_, lean_object* v_b_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
uint8_t v___x_2955_; 
v___x_2955_ = lean_usize_dec_lt(v_i_2945_, v_sz_2944_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; 
v___x_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2956_, 0, v_b_2946_);
return v___x_2956_;
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2958_; 
v_a_2957_ = lean_array_uget_borrowed(v_as_2943_, v_i_2945_);
lean_inc(v_a_2957_);
v___x_2958_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__0(v_a_2957_, v_b_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2971_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_2971_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2971_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
if (lean_obj_tag(v_a_2959_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2965_; 
v_a_2963_ = lean_ctor_get(v_a_2959_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v_a_2959_, 1);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v_a_2963_);
v___x_2965_ = v___x_2961_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2963_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
else
{
lean_object* v_a_2967_; size_t v___x_2968_; size_t v___x_2969_; 
lean_del_object(v___x_2961_);
v_a_2967_ = lean_ctor_get(v_a_2959_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v_a_2959_, 1);
v___x_2968_ = ((size_t)1ULL);
v___x_2969_ = lean_usize_add(v_i_2945_, v___x_2968_);
v_i_2945_ = v___x_2969_;
v_b_2946_ = v_a_2967_;
goto _start;
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
v_a_2972_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2958_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2958_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__1___boxed(lean_object* v_as_2980_, lean_object* v_sz_2981_, lean_object* v_i_2982_, lean_object* v_b_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
size_t v_sz_boxed_2992_; size_t v_i_boxed_2993_; lean_object* v_res_2994_; 
v_sz_boxed_2992_ = lean_unbox_usize(v_sz_2981_);
lean_dec(v_sz_2981_);
v_i_boxed_2993_ = lean_unbox_usize(v_i_2982_);
lean_dec(v_i_2982_);
v_res_2994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__1(v_as_2980_, v_sz_boxed_2992_, v_i_boxed_2993_, v_b_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v_as_2980_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement(lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v___x_3003_; lean_object* v_sorts_3004_; lean_object* v_buckets_3005_; lean_object* v___x_3006_; size_t v_sz_3007_; size_t v___x_3008_; lean_object* v___x_3009_; 
v___x_3003_ = lean_st_ref_get(v_a_2995_);
v_sorts_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc_ref(v_sorts_3004_);
lean_dec(v___x_3003_);
v_buckets_3005_ = lean_ctor_get(v_sorts_3004_, 1);
lean_inc_ref(v_buckets_3005_);
lean_dec_ref(v_sorts_3004_);
v___x_3006_ = lean_box(0);
v_sz_3007_ = lean_array_size(v_buckets_3005_);
v___x_3008_ = ((size_t)0ULL);
v___x_3009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement_spec__1(v_buckets_3005_, v_sz_3007_, v___x_3008_, v___x_3006_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_);
lean_dec_ref(v_buckets_3005_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; 
v_unused_3017_ = lean_ctor_get(v___x_3009_, 0);
lean_dec(v_unused_3017_);
v___x_3011_ = v___x_3009_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_dec(v___x_3009_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 0, v___x_3006_);
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3006_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
else
{
return v___x_3009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement___boxed(lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement(v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
lean_dec(v_a_3018_);
return v_res_3026_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__0___redArg(lean_object* v_m_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_buckets_3029_; lean_object* v___x_3030_; size_t v___x_3031_; size_t v___x_3032_; size_t v___x_3033_; uint64_t v___x_3034_; uint64_t v___x_3035_; uint64_t v___x_3036_; uint64_t v_fold_3037_; uint64_t v___x_3038_; uint64_t v___x_3039_; uint64_t v___x_3040_; size_t v___x_3041_; size_t v___x_3042_; size_t v___x_3043_; size_t v___x_3044_; size_t v___x_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; 
v_buckets_3029_ = lean_ctor_get(v_m_3027_, 1);
v___x_3030_ = lean_array_get_size(v_buckets_3029_);
v___x_3031_ = lean_ptr_addr(v_a_3028_);
v___x_3032_ = ((size_t)3ULL);
v___x_3033_ = lean_usize_shift_right(v___x_3031_, v___x_3032_);
v___x_3034_ = lean_usize_to_uint64(v___x_3033_);
v___x_3035_ = 32ULL;
v___x_3036_ = lean_uint64_shift_right(v___x_3034_, v___x_3035_);
v_fold_3037_ = lean_uint64_xor(v___x_3034_, v___x_3036_);
v___x_3038_ = 16ULL;
v___x_3039_ = lean_uint64_shift_right(v_fold_3037_, v___x_3038_);
v___x_3040_ = lean_uint64_xor(v_fold_3037_, v___x_3039_);
v___x_3041_ = lean_uint64_to_usize(v___x_3040_);
v___x_3042_ = lean_usize_of_nat(v___x_3030_);
v___x_3043_ = ((size_t)1ULL);
v___x_3044_ = lean_usize_sub(v___x_3042_, v___x_3043_);
v___x_3045_ = lean_usize_land(v___x_3041_, v___x_3044_);
v___x_3046_ = lean_array_uget_borrowed(v_buckets_3029_, v___x_3045_);
v___x_3047_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__1_spec__4___redArg(v_a_3028_, v___x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__0___redArg___boxed(lean_object* v_m_3048_, lean_object* v_a_3049_){
_start:
{
uint8_t v_res_3050_; lean_object* v_r_3051_; 
v_res_3050_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__0___redArg(v_m_3048_, v_a_3049_);
lean_dec_ref(v_a_3049_);
lean_dec_ref(v_m_3048_);
v_r_3051_ = lean_box(v_res_3050_);
return v_r_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__1(lean_object* v_usedElements_3052_, lean_object* v_as_3053_, size_t v_i_3054_, size_t v_stop_3055_, lean_object* v_b_3056_){
_start:
{
lean_object* v___y_3058_; uint8_t v___x_3062_; 
v___x_3062_ = lean_usize_dec_eq(v_i_3054_, v_stop_3055_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3063_ = lean_array_uget_borrowed(v_as_3053_, v_i_3054_);
v___x_3064_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__0___redArg(v_usedElements_3052_, v___x_3063_);
if (v___x_3064_ == 0)
{
v___y_3058_ = v_b_3056_;
goto v___jp_3057_;
}
else
{
lean_object* v___x_3065_; 
lean_inc(v___x_3063_);
v___x_3065_ = lean_array_push(v_b_3056_, v___x_3063_);
v___y_3058_ = v___x_3065_;
goto v___jp_3057_;
}
}
else
{
return v_b_3056_;
}
v___jp_3057_:
{
size_t v___x_3059_; size_t v___x_3060_; 
v___x_3059_ = ((size_t)1ULL);
v___x_3060_ = lean_usize_add(v_i_3054_, v___x_3059_);
v_i_3054_ = v___x_3060_;
v_b_3056_ = v___y_3058_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__1___boxed(lean_object* v_usedElements_3066_, lean_object* v_as_3067_, lean_object* v_i_3068_, lean_object* v_stop_3069_, lean_object* v_b_3070_){
_start:
{
size_t v_i_boxed_3071_; size_t v_stop_boxed_3072_; lean_object* v_res_3073_; 
v_i_boxed_3071_ = lean_unbox_usize(v_i_3068_);
lean_dec(v_i_3068_);
v_stop_boxed_3072_ = lean_unbox_usize(v_stop_3069_);
lean_dec(v_stop_3069_);
v_res_3073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__1(v_usedElements_3066_, v_as_3067_, v_i_boxed_3071_, v_stop_boxed_3072_, v_b_3070_);
lean_dec_ref(v_as_3067_);
lean_dec_ref(v_usedElements_3066_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__2___redArg(lean_object* v_usedElements_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v___y_3077_){
_start:
{
if (lean_obj_tag(v_a_3075_) == 0)
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3079_, 0, v_a_3076_);
v___x_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
return v___x_3080_;
}
else
{
lean_object* v_value_3081_; lean_object* v_key_3082_; lean_object* v_tail_3083_; lean_object* v_type_3084_; lean_object* v_level_3085_; lean_object* v_elements_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3129_; 
v_value_3081_ = lean_ctor_get(v_a_3075_, 1);
lean_inc(v_value_3081_);
v_key_3082_ = lean_ctor_get(v_a_3075_, 0);
lean_inc(v_key_3082_);
v_tail_3083_ = lean_ctor_get(v_a_3075_, 2);
lean_inc(v_tail_3083_);
lean_dec_ref_known(v_a_3075_, 3);
v_type_3084_ = lean_ctor_get(v_value_3081_, 0);
v_level_3085_ = lean_ctor_get(v_value_3081_, 1);
v_elements_3086_ = lean_ctor_get(v_value_3081_, 2);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_value_3081_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3088_ = v_value_3081_;
v_isShared_3089_ = v_isSharedCheck_3129_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_elements_3086_);
lean_inc(v_level_3085_);
lean_inc(v_type_3084_);
lean_dec(v_value_3081_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3129_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3090_; lean_object* v___y_3092_; lean_object* v___x_3116_; lean_object* v___y_3118_; lean_object* v___x_3123_; lean_object* v___x_3124_; uint8_t v___x_3125_; 
v___x_3090_ = lean_box(0);
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3123_ = lean_array_get_size(v_elements_3086_);
v___x_3124_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortCandidate_default___closed__3));
v___x_3125_ = lean_nat_dec_lt(v___x_3116_, v___x_3123_);
if (v___x_3125_ == 0)
{
v___y_3118_ = v___x_3124_;
goto v___jp_3117_;
}
else
{
size_t v___x_3126_; size_t v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = ((size_t)0ULL);
v___x_3127_ = lean_usize_of_nat(v___x_3123_);
v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__1(v_usedElements_3074_, v_elements_3086_, v___x_3126_, v___x_3127_, v___x_3124_);
v___y_3118_ = v___x_3128_;
goto v___jp_3117_;
}
v___jp_3091_:
{
lean_object* v___x_3093_; lean_object* v_sorts_3094_; lean_object* v_sortIds_3095_; lean_object* v_nextSortId_3096_; lean_object* v_elements_3097_; lean_object* v_preds_3098_; lean_object* v_usedElements_3099_; lean_object* v_groundFacts_3100_; lean_object* v_quantifiedFacts_3101_; lean_object* v_remainingHyps_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3115_; 
v___x_3093_ = lean_st_ref_take(v___y_3077_);
v_sorts_3094_ = lean_ctor_get(v___x_3093_, 0);
v_sortIds_3095_ = lean_ctor_get(v___x_3093_, 1);
v_nextSortId_3096_ = lean_ctor_get(v___x_3093_, 2);
v_elements_3097_ = lean_ctor_get(v___x_3093_, 3);
v_preds_3098_ = lean_ctor_get(v___x_3093_, 4);
v_usedElements_3099_ = lean_ctor_get(v___x_3093_, 5);
v_groundFacts_3100_ = lean_ctor_get(v___x_3093_, 6);
v_quantifiedFacts_3101_ = lean_ctor_get(v___x_3093_, 7);
v_remainingHyps_3102_ = lean_ctor_get(v___x_3093_, 8);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3104_ = v___x_3093_;
v_isShared_3105_ = v_isSharedCheck_3115_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_remainingHyps_3102_);
lean_inc(v_quantifiedFacts_3101_);
lean_inc(v_groundFacts_3100_);
lean_inc(v_usedElements_3099_);
lean_inc(v_preds_3098_);
lean_inc(v_elements_3097_);
lean_inc(v_nextSortId_3096_);
lean_inc(v_sortIds_3095_);
lean_inc(v_sorts_3094_);
lean_dec(v___x_3093_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3115_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 2, v___y_3092_);
v___x_3107_ = v___x_3088_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_type_3084_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_level_3085_);
lean_ctor_set(v_reuseFailAlloc_3114_, 2, v___y_3092_);
v___x_3107_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3108_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0___redArg(v_sorts_3094_, v_key_3082_, v___x_3107_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v___x_3108_);
v___x_3110_ = v___x_3104_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3108_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_sortIds_3095_);
lean_ctor_set(v_reuseFailAlloc_3113_, 2, v_nextSortId_3096_);
lean_ctor_set(v_reuseFailAlloc_3113_, 3, v_elements_3097_);
lean_ctor_set(v_reuseFailAlloc_3113_, 4, v_preds_3098_);
lean_ctor_set(v_reuseFailAlloc_3113_, 5, v_usedElements_3099_);
lean_ctor_set(v_reuseFailAlloc_3113_, 6, v_groundFacts_3100_);
lean_ctor_set(v_reuseFailAlloc_3113_, 7, v_quantifiedFacts_3101_);
lean_ctor_set(v_reuseFailAlloc_3113_, 8, v_remainingHyps_3102_);
v___x_3110_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3111_; 
v___x_3111_ = lean_st_ref_put(v___y_3077_, v___x_3110_);
v_a_3075_ = v_tail_3083_;
v_a_3076_ = v___x_3090_;
goto _start;
}
}
}
}
v___jp_3117_:
{
lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3119_ = lean_array_get_size(v___y_3118_);
v___x_3120_ = lean_nat_dec_eq(v___x_3119_, v___x_3116_);
if (v___x_3120_ == 0)
{
lean_dec_ref(v_elements_3086_);
v___y_3092_ = v___y_3118_;
goto v___jp_3091_;
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
lean_dec_ref(v___y_3118_);
v___x_3121_ = lean_unsigned_to_nat(1u);
v___x_3122_ = l_Array_extract___redArg(v_elements_3086_, v___x_3116_, v___x_3121_);
lean_dec_ref(v_elements_3086_);
v___y_3092_ = v___x_3122_;
goto v___jp_3091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__2___redArg___boxed(lean_object* v_usedElements_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__2___redArg(v_usedElements_3130_, v_a_3131_, v_a_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v_usedElements_3130_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__3(lean_object* v_usedElements_3136_, lean_object* v_as_3137_, size_t v_sz_3138_, size_t v_i_3139_, lean_object* v_b_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
uint8_t v___x_3149_; 
v___x_3149_ = lean_usize_dec_lt(v_i_3139_, v_sz_3138_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; 
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v_b_3140_);
return v___x_3150_;
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3152_; 
v_a_3151_ = lean_array_uget_borrowed(v_as_3137_, v_i_3139_);
lean_inc(v_a_3151_);
v___x_3152_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__2___redArg(v_usedElements_3136_, v_a_3151_, v_b_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3165_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3165_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3165_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
if (lean_obj_tag(v_a_3153_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3159_; 
v_a_3157_ = lean_ctor_get(v_a_3153_, 0);
lean_inc(v_a_3157_);
lean_dec_ref_known(v_a_3153_, 1);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v_a_3157_);
v___x_3159_ = v___x_3155_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
else
{
lean_object* v_a_3161_; size_t v___x_3162_; size_t v___x_3163_; 
lean_del_object(v___x_3155_);
v_a_3161_ = lean_ctor_get(v_a_3153_, 0);
lean_inc(v_a_3161_);
lean_dec_ref_known(v_a_3153_, 1);
v___x_3162_ = ((size_t)1ULL);
v___x_3163_ = lean_usize_add(v_i_3139_, v___x_3162_);
v_i_3139_ = v___x_3163_;
v_b_3140_ = v_a_3161_;
goto _start;
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
v_a_3166_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3152_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3152_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__3___boxed(lean_object* v_usedElements_3174_, lean_object* v_as_3175_, lean_object* v_sz_3176_, lean_object* v_i_3177_, lean_object* v_b_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
size_t v_sz_boxed_3187_; size_t v_i_boxed_3188_; lean_object* v_res_3189_; 
v_sz_boxed_3187_ = lean_unbox_usize(v_sz_3176_);
lean_dec(v_sz_3176_);
v_i_boxed_3188_ = lean_unbox_usize(v_i_3177_);
lean_dec(v_i_3177_);
v_res_3189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__3(v_usedElements_3174_, v_as_3175_, v_sz_boxed_3187_, v_i_boxed_3188_, v_b_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v_as_3175_);
lean_dec_ref(v_usedElements_3174_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements(lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_){
_start:
{
lean_object* v___x_3198_; lean_object* v_sorts_3199_; lean_object* v_usedElements_3200_; lean_object* v_buckets_3201_; lean_object* v___x_3202_; size_t v_sz_3203_; size_t v___x_3204_; lean_object* v___x_3205_; 
v___x_3198_ = lean_st_ref_get(v_a_3190_);
v_sorts_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc_ref(v_sorts_3199_);
v_usedElements_3200_ = lean_ctor_get(v___x_3198_, 5);
lean_inc_ref(v_usedElements_3200_);
lean_dec(v___x_3198_);
v_buckets_3201_ = lean_ctor_get(v_sorts_3199_, 1);
lean_inc_ref(v_buckets_3201_);
lean_dec_ref(v_sorts_3199_);
v___x_3202_ = lean_box(0);
v_sz_3203_ = lean_array_size(v_buckets_3201_);
v___x_3204_ = ((size_t)0ULL);
v___x_3205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__3(v_usedElements_3200_, v_buckets_3201_, v_sz_3203_, v___x_3204_, v___x_3202_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
lean_dec_ref(v_buckets_3201_);
lean_dec_ref(v_usedElements_3200_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v___x_3205_, 0);
lean_dec(v_unused_3213_);
v___x_3207_ = v___x_3205_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_dec(v___x_3205_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v___x_3202_);
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3202_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
else
{
return v___x_3205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements___boxed(lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements(v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
lean_dec(v_a_3220_);
lean_dec_ref(v_a_3219_);
lean_dec(v_a_3218_);
lean_dec_ref(v_a_3217_);
lean_dec(v_a_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_a_3214_);
return v_res_3222_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__0(lean_object* v_00_u03b2_3223_, lean_object* v_m_3224_, lean_object* v_a_3225_){
_start:
{
uint8_t v___x_3226_; 
v___x_3226_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__0___redArg(v_m_3224_, v_a_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__0___boxed(lean_object* v_00_u03b2_3227_, lean_object* v_m_3228_, lean_object* v_a_3229_){
_start:
{
uint8_t v_res_3230_; lean_object* v_r_3231_; 
v_res_3230_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__0(v_00_u03b2_3227_, v_m_3228_, v_a_3229_);
lean_dec_ref(v_a_3229_);
lean_dec_ref(v_m_3228_);
v_r_3231_ = lean_box(v_res_3230_);
return v_r_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__2(lean_object* v_usedElements_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__2___redArg(v_usedElements_3232_, v_a_3233_, v_a_3234_, v___y_3235_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__2___boxed(lean_object* v_usedElements_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements_spec__2(v_usedElements_3244_, v_a_3245_, v_a_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v_usedElements_3244_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__2___redArg(lean_object* v_a_3256_, lean_object* v_b_3257_, lean_object* v_x_3258_){
_start:
{
if (lean_obj_tag(v_x_3258_) == 0)
{
lean_dec(v_b_3257_);
lean_dec_ref(v_a_3256_);
return v_x_3258_;
}
else
{
lean_object* v_key_3259_; lean_object* v_value_3260_; lean_object* v_tail_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3273_; 
v_key_3259_ = lean_ctor_get(v_x_3258_, 0);
v_value_3260_ = lean_ctor_get(v_x_3258_, 1);
v_tail_3261_ = lean_ctor_get(v_x_3258_, 2);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_x_3258_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3263_ = v_x_3258_;
v_isShared_3264_ = v_isSharedCheck_3273_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_tail_3261_);
lean_inc(v_value_3260_);
lean_inc(v_key_3259_);
lean_dec(v_x_3258_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3273_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
uint8_t v___x_3265_; 
v___x_3265_ = lean_expr_eqv(v_key_3259_, v_a_3256_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3266_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__2___redArg(v_a_3256_, v_b_3257_, v_tail_3261_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 2, v___x_3266_);
v___x_3268_ = v___x_3263_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_key_3259_);
lean_ctor_set(v_reuseFailAlloc_3269_, 1, v_value_3260_);
lean_ctor_set(v_reuseFailAlloc_3269_, 2, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
else
{
lean_object* v___x_3271_; 
lean_dec(v_value_3260_);
lean_dec(v_key_3259_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 1, v_b_3257_);
lean_ctor_set(v___x_3263_, 0, v_a_3256_);
v___x_3271_ = v___x_3263_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3256_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_b_3257_);
lean_ctor_set(v_reuseFailAlloc_3272_, 2, v_tail_3261_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___redArg(lean_object* v_a_3274_, lean_object* v_x_3275_){
_start:
{
if (lean_obj_tag(v_x_3275_) == 0)
{
uint8_t v___x_3276_; 
v___x_3276_ = 0;
return v___x_3276_;
}
else
{
lean_object* v_key_3277_; lean_object* v_tail_3278_; uint8_t v___x_3279_; 
v_key_3277_ = lean_ctor_get(v_x_3275_, 0);
v_tail_3278_ = lean_ctor_get(v_x_3275_, 2);
v___x_3279_ = lean_expr_eqv(v_key_3277_, v_a_3274_);
if (v___x_3279_ == 0)
{
v_x_3275_ = v_tail_3278_;
goto _start;
}
else
{
return v___x_3279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___redArg___boxed(lean_object* v_a_3281_, lean_object* v_x_3282_){
_start:
{
uint8_t v_res_3283_; lean_object* v_r_3284_; 
v_res_3283_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___redArg(v_a_3281_, v_x_3282_);
lean_dec(v_x_3282_);
lean_dec_ref(v_a_3281_);
v_r_3284_ = lean_box(v_res_3283_);
return v_r_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2_spec__10___redArg(lean_object* v_x_3285_, lean_object* v_x_3286_){
_start:
{
if (lean_obj_tag(v_x_3286_) == 0)
{
return v_x_3285_;
}
else
{
lean_object* v_key_3287_; lean_object* v_value_3288_; lean_object* v_tail_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3312_; 
v_key_3287_ = lean_ctor_get(v_x_3286_, 0);
v_value_3288_ = lean_ctor_get(v_x_3286_, 1);
v_tail_3289_ = lean_ctor_get(v_x_3286_, 2);
v_isSharedCheck_3312_ = !lean_is_exclusive(v_x_3286_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3291_ = v_x_3286_;
v_isShared_3292_ = v_isSharedCheck_3312_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_tail_3289_);
lean_inc(v_value_3288_);
lean_inc(v_key_3287_);
lean_dec(v_x_3286_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3312_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; uint64_t v___x_3294_; uint64_t v___x_3295_; uint64_t v___x_3296_; uint64_t v_fold_3297_; uint64_t v___x_3298_; uint64_t v___x_3299_; uint64_t v___x_3300_; size_t v___x_3301_; size_t v___x_3302_; size_t v___x_3303_; size_t v___x_3304_; size_t v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3293_ = lean_array_get_size(v_x_3285_);
v___x_3294_ = l_Lean_Expr_hash(v_key_3287_);
v___x_3295_ = 32ULL;
v___x_3296_ = lean_uint64_shift_right(v___x_3294_, v___x_3295_);
v_fold_3297_ = lean_uint64_xor(v___x_3294_, v___x_3296_);
v___x_3298_ = 16ULL;
v___x_3299_ = lean_uint64_shift_right(v_fold_3297_, v___x_3298_);
v___x_3300_ = lean_uint64_xor(v_fold_3297_, v___x_3299_);
v___x_3301_ = lean_uint64_to_usize(v___x_3300_);
v___x_3302_ = lean_usize_of_nat(v___x_3293_);
v___x_3303_ = ((size_t)1ULL);
v___x_3304_ = lean_usize_sub(v___x_3302_, v___x_3303_);
v___x_3305_ = lean_usize_land(v___x_3301_, v___x_3304_);
v___x_3306_ = lean_array_uget_borrowed(v_x_3285_, v___x_3305_);
lean_inc(v___x_3306_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 2, v___x_3306_);
v___x_3308_ = v___x_3291_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_key_3287_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v_value_3288_);
lean_ctor_set(v_reuseFailAlloc_3311_, 2, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3309_; 
v___x_3309_ = lean_array_uset(v_x_3285_, v___x_3305_, v___x_3308_);
v_x_3285_ = v___x_3309_;
v_x_3286_ = v_tail_3289_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3313_, lean_object* v_source_3314_, lean_object* v_target_3315_){
_start:
{
lean_object* v___x_3316_; uint8_t v___x_3317_; 
v___x_3316_ = lean_array_get_size(v_source_3314_);
v___x_3317_ = lean_nat_dec_lt(v_i_3313_, v___x_3316_);
if (v___x_3317_ == 0)
{
lean_dec_ref(v_source_3314_);
lean_dec(v_i_3313_);
return v_target_3315_;
}
else
{
lean_object* v_es_3318_; lean_object* v___x_3319_; lean_object* v_source_3320_; lean_object* v_target_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v_es_3318_ = lean_array_fget(v_source_3314_, v_i_3313_);
v___x_3319_ = lean_box(0);
v_source_3320_ = lean_array_fset(v_source_3314_, v_i_3313_, v___x_3319_);
v_target_3321_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2_spec__10___redArg(v_target_3315_, v_es_3318_);
v___x_3322_ = lean_unsigned_to_nat(1u);
v___x_3323_ = lean_nat_add(v_i_3313_, v___x_3322_);
lean_dec(v_i_3313_);
v_i_3313_ = v___x_3323_;
v_source_3314_ = v_source_3320_;
v_target_3315_ = v_target_3321_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1___redArg(lean_object* v_data_3325_){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v_nbuckets_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3326_ = lean_array_get_size(v_data_3325_);
v___x_3327_ = lean_unsigned_to_nat(2u);
v_nbuckets_3328_ = lean_nat_mul(v___x_3326_, v___x_3327_);
v___x_3329_ = lean_unsigned_to_nat(0u);
v___x_3330_ = lean_box(0);
v___x_3331_ = lean_mk_array(v_nbuckets_3328_, v___x_3330_);
v___x_3332_ = lean_array_propagate_mark(v_data_3325_, v___x_3331_);
v___x_3333_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2___redArg(v___x_3329_, v_data_3325_, v___x_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0___redArg(lean_object* v_m_3334_, lean_object* v_a_3335_, lean_object* v_b_3336_){
_start:
{
lean_object* v_size_3337_; lean_object* v_buckets_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3381_; 
v_size_3337_ = lean_ctor_get(v_m_3334_, 0);
v_buckets_3338_ = lean_ctor_get(v_m_3334_, 1);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_m_3334_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3340_ = v_m_3334_;
v_isShared_3341_ = v_isSharedCheck_3381_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_buckets_3338_);
lean_inc(v_size_3337_);
lean_dec(v_m_3334_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3381_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; uint64_t v___x_3343_; uint64_t v___x_3344_; uint64_t v___x_3345_; uint64_t v_fold_3346_; uint64_t v___x_3347_; uint64_t v___x_3348_; uint64_t v___x_3349_; size_t v___x_3350_; size_t v___x_3351_; size_t v___x_3352_; size_t v___x_3353_; size_t v___x_3354_; lean_object* v_bkt_3355_; uint8_t v___x_3356_; 
v___x_3342_ = lean_array_get_size(v_buckets_3338_);
v___x_3343_ = l_Lean_Expr_hash(v_a_3335_);
v___x_3344_ = 32ULL;
v___x_3345_ = lean_uint64_shift_right(v___x_3343_, v___x_3344_);
v_fold_3346_ = lean_uint64_xor(v___x_3343_, v___x_3345_);
v___x_3347_ = 16ULL;
v___x_3348_ = lean_uint64_shift_right(v_fold_3346_, v___x_3347_);
v___x_3349_ = lean_uint64_xor(v_fold_3346_, v___x_3348_);
v___x_3350_ = lean_uint64_to_usize(v___x_3349_);
v___x_3351_ = lean_usize_of_nat(v___x_3342_);
v___x_3352_ = ((size_t)1ULL);
v___x_3353_ = lean_usize_sub(v___x_3351_, v___x_3352_);
v___x_3354_ = lean_usize_land(v___x_3350_, v___x_3353_);
v_bkt_3355_ = lean_array_uget_borrowed(v_buckets_3338_, v___x_3354_);
v___x_3356_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___redArg(v_a_3335_, v_bkt_3355_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; lean_object* v_size_x27_3358_; lean_object* v___x_3359_; lean_object* v_buckets_x27_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; 
v___x_3357_ = lean_unsigned_to_nat(1u);
v_size_x27_3358_ = lean_nat_add(v_size_3337_, v___x_3357_);
lean_dec(v_size_3337_);
lean_inc(v_bkt_3355_);
v___x_3359_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3359_, 0, v_a_3335_);
lean_ctor_set(v___x_3359_, 1, v_b_3336_);
lean_ctor_set(v___x_3359_, 2, v_bkt_3355_);
v_buckets_x27_3360_ = lean_array_uset(v_buckets_3338_, v___x_3354_, v___x_3359_);
v___x_3361_ = lean_unsigned_to_nat(4u);
v___x_3362_ = lean_nat_mul(v_size_x27_3358_, v___x_3361_);
v___x_3363_ = lean_unsigned_to_nat(3u);
v___x_3364_ = lean_nat_div(v___x_3362_, v___x_3363_);
lean_dec(v___x_3362_);
v___x_3365_ = lean_array_get_size(v_buckets_x27_3360_);
v___x_3366_ = lean_nat_dec_le(v___x_3364_, v___x_3365_);
lean_dec(v___x_3364_);
if (v___x_3366_ == 0)
{
lean_object* v_val_3367_; lean_object* v___x_3369_; 
v_val_3367_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1___redArg(v_buckets_x27_3360_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 1, v_val_3367_);
lean_ctor_set(v___x_3340_, 0, v_size_x27_3358_);
v___x_3369_ = v___x_3340_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_size_x27_3358_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_val_3367_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
else
{
lean_object* v___x_3372_; 
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 1, v_buckets_x27_3360_);
lean_ctor_set(v___x_3340_, 0, v_size_x27_3358_);
v___x_3372_ = v___x_3340_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_size_x27_3358_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_buckets_x27_3360_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
else
{
lean_object* v___x_3374_; lean_object* v_buckets_x27_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3379_; 
lean_inc(v_bkt_3355_);
v___x_3374_ = lean_box(0);
v_buckets_x27_3375_ = lean_array_uset(v_buckets_3338_, v___x_3354_, v___x_3374_);
v___x_3376_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__2___redArg(v_a_3335_, v_b_3336_, v_bkt_3355_);
v___x_3377_ = lean_array_uset(v_buckets_x27_3375_, v___x_3354_, v___x_3376_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 1, v___x_3377_);
v___x_3379_ = v___x_3340_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_size_3337_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___redArg(lean_object* v_m_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v_buckets_3384_; lean_object* v___x_3385_; uint64_t v___x_3386_; uint64_t v___x_3387_; uint64_t v___x_3388_; uint64_t v_fold_3389_; uint64_t v___x_3390_; uint64_t v___x_3391_; uint64_t v___x_3392_; size_t v___x_3393_; size_t v___x_3394_; size_t v___x_3395_; size_t v___x_3396_; size_t v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
v_buckets_3384_ = lean_ctor_get(v_m_3382_, 1);
v___x_3385_ = lean_array_get_size(v_buckets_3384_);
v___x_3386_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_a_3383_);
v___x_3387_ = 32ULL;
v___x_3388_ = lean_uint64_shift_right(v___x_3386_, v___x_3387_);
v_fold_3389_ = lean_uint64_xor(v___x_3386_, v___x_3388_);
v___x_3390_ = 16ULL;
v___x_3391_ = lean_uint64_shift_right(v_fold_3389_, v___x_3390_);
v___x_3392_ = lean_uint64_xor(v_fold_3389_, v___x_3391_);
v___x_3393_ = lean_uint64_to_usize(v___x_3392_);
v___x_3394_ = lean_usize_of_nat(v___x_3385_);
v___x_3395_ = ((size_t)1ULL);
v___x_3396_ = lean_usize_sub(v___x_3394_, v___x_3395_);
v___x_3397_ = lean_usize_land(v___x_3393_, v___x_3396_);
v___x_3398_ = lean_array_uget_borrowed(v_buckets_3384_, v___x_3397_);
v___x_3399_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0_spec__0___redArg(v_a_3383_, v___x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___redArg___boxed(lean_object* v_m_3400_, lean_object* v_a_3401_){
_start:
{
uint8_t v_res_3402_; lean_object* v_r_3403_; 
v_res_3402_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___redArg(v_m_3400_, v_a_3401_);
lean_dec(v_a_3401_);
lean_dec_ref(v_m_3400_);
v_r_3403_ = lean_box(v_res_3402_);
return v_r_3403_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__2(lean_object* v___x_3404_, lean_object* v_as_3405_, size_t v_i_3406_, size_t v_stop_3407_){
_start:
{
uint8_t v___x_3408_; 
v___x_3408_ = lean_usize_dec_eq(v_i_3406_, v_stop_3407_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; uint8_t v___x_3410_; 
v___x_3409_ = lean_array_uget_borrowed(v_as_3405_, v_i_3406_);
v___x_3410_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___redArg(v___x_3404_, v___x_3409_);
if (v___x_3410_ == 0)
{
uint8_t v___x_3411_; 
v___x_3411_ = 1;
return v___x_3411_;
}
else
{
size_t v___x_3412_; size_t v___x_3413_; 
v___x_3412_ = ((size_t)1ULL);
v___x_3413_ = lean_usize_add(v_i_3406_, v___x_3412_);
v_i_3406_ = v___x_3413_;
goto _start;
}
}
else
{
uint8_t v___x_3415_; 
v___x_3415_ = 0;
return v___x_3415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__2___boxed(lean_object* v___x_3416_, lean_object* v_as_3417_, lean_object* v_i_3418_, lean_object* v_stop_3419_){
_start:
{
size_t v_i_boxed_3420_; size_t v_stop_boxed_3421_; uint8_t v_res_3422_; lean_object* v_r_3423_; 
v_i_boxed_3420_ = lean_unbox_usize(v_i_3418_);
lean_dec(v_i_3418_);
v_stop_boxed_3421_ = lean_unbox_usize(v_stop_3419_);
lean_dec(v_stop_3419_);
v_res_3422_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__2(v___x_3416_, v_as_3417_, v_i_boxed_3420_, v_stop_boxed_3421_);
lean_dec_ref(v_as_3417_);
lean_dec_ref(v___x_3416_);
v_r_3423_ = lean_box(v_res_3422_);
return v_r_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___redArg(lean_object* v_a_3424_, lean_object* v_a_3425_){
_start:
{
if (lean_obj_tag(v_a_3424_) == 0)
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3427_, 0, v_a_3425_);
v___x_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
return v___x_3428_;
}
else
{
lean_object* v_value_3429_; lean_object* v_key_3430_; lean_object* v_tail_3431_; lean_object* v_argumentSorts_3432_; lean_object* v_sortInfo_3433_; lean_object* v_sortMap_3434_; lean_object* v_predInfo_3435_; lean_object* v_groundFacts_3436_; lean_object* v_quantifiedFacts_3437_; lean_object* v___x_3442_; lean_object* v___x_3443_; uint8_t v___x_3444_; 
v_value_3429_ = lean_ctor_get(v_a_3424_, 1);
lean_inc(v_value_3429_);
v_key_3430_ = lean_ctor_get(v_a_3424_, 0);
lean_inc(v_key_3430_);
v_tail_3431_ = lean_ctor_get(v_a_3424_, 2);
lean_inc(v_tail_3431_);
lean_dec_ref_known(v_a_3424_, 3);
v_argumentSorts_3432_ = lean_ctor_get(v_value_3429_, 0);
v_sortInfo_3433_ = lean_ctor_get(v_a_3425_, 0);
v_sortMap_3434_ = lean_ctor_get(v_a_3425_, 1);
v_predInfo_3435_ = lean_ctor_get(v_a_3425_, 2);
v_groundFacts_3436_ = lean_ctor_get(v_a_3425_, 3);
v_quantifiedFacts_3437_ = lean_ctor_get(v_a_3425_, 4);
v___x_3442_ = lean_unsigned_to_nat(0u);
v___x_3443_ = lean_array_get_size(v_argumentSorts_3432_);
v___x_3444_ = lean_nat_dec_lt(v___x_3442_, v___x_3443_);
if (v___x_3444_ == 0)
{
lean_inc_ref(v_quantifiedFacts_3437_);
lean_inc_ref(v_groundFacts_3436_);
lean_inc_ref(v_predInfo_3435_);
lean_inc_ref(v_sortMap_3434_);
lean_inc_ref(v_sortInfo_3433_);
lean_dec_ref(v_a_3425_);
goto v___jp_3438_;
}
else
{
if (v___x_3444_ == 0)
{
lean_inc_ref(v_quantifiedFacts_3437_);
lean_inc_ref(v_groundFacts_3436_);
lean_inc_ref(v_predInfo_3435_);
lean_inc_ref(v_sortMap_3434_);
lean_inc_ref(v_sortInfo_3433_);
lean_dec_ref(v_a_3425_);
goto v___jp_3438_;
}
else
{
size_t v___x_3445_; size_t v___x_3446_; uint8_t v___x_3447_; 
v___x_3445_ = ((size_t)0ULL);
v___x_3446_ = lean_usize_of_nat(v___x_3443_);
v___x_3447_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__2(v_sortInfo_3433_, v_argumentSorts_3432_, v___x_3445_, v___x_3446_);
if (v___x_3447_ == 0)
{
lean_inc_ref(v_quantifiedFacts_3437_);
lean_inc_ref(v_groundFacts_3436_);
lean_inc_ref(v_predInfo_3435_);
lean_inc_ref(v_sortMap_3434_);
lean_inc_ref(v_sortInfo_3433_);
lean_dec_ref(v_a_3425_);
goto v___jp_3438_;
}
else
{
lean_dec(v_key_3430_);
lean_dec(v_value_3429_);
v_a_3424_ = v_tail_3431_;
goto _start;
}
}
}
v___jp_3438_:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0___redArg(v_predInfo_3435_, v_key_3430_, v_value_3429_);
v___x_3440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3440_, 0, v_sortInfo_3433_);
lean_ctor_set(v___x_3440_, 1, v_sortMap_3434_);
lean_ctor_set(v___x_3440_, 2, v___x_3439_);
lean_ctor_set(v___x_3440_, 3, v_groundFacts_3436_);
lean_ctor_set(v___x_3440_, 4, v_quantifiedFacts_3437_);
v_a_3424_ = v_tail_3431_;
v_a_3425_ = v___x_3440_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___redArg___boxed(lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___redArg(v_a_3449_, v_a_3450_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__7(lean_object* v_as_3453_, size_t v_sz_3454_, size_t v_i_3455_, lean_object* v_b_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
uint8_t v___x_3465_; 
v___x_3465_ = lean_usize_dec_lt(v_i_3455_, v_sz_3454_);
if (v___x_3465_ == 0)
{
lean_object* v___x_3466_; 
v___x_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3466_, 0, v_b_3456_);
return v___x_3466_;
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3468_; 
v_a_3467_ = lean_array_uget_borrowed(v_as_3453_, v_i_3455_);
lean_inc(v_a_3467_);
v___x_3468_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___redArg(v_a_3467_, v_b_3456_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3481_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3471_ = v___x_3468_;
v_isShared_3472_ = v_isSharedCheck_3481_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3468_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3481_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
if (lean_obj_tag(v_a_3469_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3475_; 
v_a_3473_ = lean_ctor_get(v_a_3469_, 0);
lean_inc(v_a_3473_);
lean_dec_ref_known(v_a_3469_, 1);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v_a_3473_);
v___x_3475_ = v___x_3471_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
else
{
lean_object* v_a_3477_; size_t v___x_3478_; size_t v___x_3479_; 
lean_del_object(v___x_3471_);
v_a_3477_ = lean_ctor_get(v_a_3469_, 0);
lean_inc(v_a_3477_);
lean_dec_ref_known(v_a_3469_, 1);
v___x_3478_ = ((size_t)1ULL);
v___x_3479_ = lean_usize_add(v_i_3455_, v___x_3478_);
v_i_3455_ = v___x_3479_;
v_b_3456_ = v_a_3477_;
goto _start;
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
v_a_3482_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3468_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3468_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__7___boxed(lean_object* v_as_3490_, lean_object* v_sz_3491_, lean_object* v_i_3492_, lean_object* v_b_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
size_t v_sz_boxed_3502_; size_t v_i_boxed_3503_; lean_object* v_res_3504_; 
v_sz_boxed_3502_ = lean_unbox_usize(v_sz_3491_);
lean_dec(v_sz_3491_);
v_i_boxed_3503_ = lean_unbox_usize(v_i_3492_);
lean_dec(v_i_3492_);
v_res_3504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__7(v_as_3490_, v_sz_boxed_3502_, v_i_boxed_3503_, v_b_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v_as_3490_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__4(lean_object* v_a_3505_, lean_object* v_as_3506_, size_t v_i_3507_, size_t v_stop_3508_, lean_object* v_b_3509_){
_start:
{
uint8_t v___x_3510_; 
v___x_3510_ = lean_usize_dec_eq(v_i_3507_, v_stop_3508_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; lean_object* v___x_3512_; size_t v___x_3513_; size_t v___x_3514_; 
v___x_3511_ = lean_array_uget_borrowed(v_as_3506_, v_i_3507_);
lean_inc(v_a_3505_);
lean_inc(v___x_3511_);
v___x_3512_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0___redArg(v_b_3509_, v___x_3511_, v_a_3505_);
v___x_3513_ = ((size_t)1ULL);
v___x_3514_ = lean_usize_add(v_i_3507_, v___x_3513_);
v_i_3507_ = v___x_3514_;
v_b_3509_ = v___x_3512_;
goto _start;
}
else
{
lean_dec(v_a_3505_);
return v_b_3509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__4___boxed(lean_object* v_a_3516_, lean_object* v_as_3517_, lean_object* v_i_3518_, lean_object* v_stop_3519_, lean_object* v_b_3520_){
_start:
{
size_t v_i_boxed_3521_; size_t v_stop_boxed_3522_; lean_object* v_res_3523_; 
v_i_boxed_3521_ = lean_unbox_usize(v_i_3518_);
lean_dec(v_i_3518_);
v_stop_boxed_3522_ = lean_unbox_usize(v_stop_3519_);
lean_dec(v_stop_3519_);
v_res_3523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__4(v_a_3516_, v_as_3517_, v_i_boxed_3521_, v_stop_boxed_3522_, v_b_3520_);
lean_dec_ref(v_as_3517_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___redArg(lean_object* v_a_3524_, lean_object* v_a_3525_){
_start:
{
if (lean_obj_tag(v_a_3524_) == 0)
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3527_, 0, v_a_3525_);
v___x_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
return v___x_3528_;
}
else
{
lean_object* v_value_3529_; lean_object* v_key_3530_; lean_object* v_tail_3531_; lean_object* v_type_3532_; lean_object* v_level_3533_; lean_object* v_elements_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3565_; 
v_value_3529_ = lean_ctor_get(v_a_3524_, 1);
lean_inc(v_value_3529_);
v_key_3530_ = lean_ctor_get(v_a_3524_, 0);
lean_inc(v_key_3530_);
v_tail_3531_ = lean_ctor_get(v_a_3524_, 2);
lean_inc(v_tail_3531_);
lean_dec_ref_known(v_a_3524_, 3);
v_type_3532_ = lean_ctor_get(v_value_3529_, 0);
v_level_3533_ = lean_ctor_get(v_value_3529_, 1);
v_elements_3534_ = lean_ctor_get(v_value_3529_, 2);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_value_3529_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3536_ = v_value_3529_;
v_isShared_3537_ = v_isSharedCheck_3565_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_elements_3534_);
lean_inc(v_level_3533_);
lean_inc(v_type_3532_);
lean_dec(v_value_3529_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3565_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v___x_3538_ = lean_array_get_size(v_elements_3534_);
v___x_3539_ = lean_unsigned_to_nat(0u);
v___x_3540_ = lean_nat_dec_eq(v___x_3538_, v___x_3539_);
if (v___x_3540_ == 0)
{
lean_object* v_sortInfo_3541_; lean_object* v_sortMap_3542_; lean_object* v_predInfo_3543_; lean_object* v_groundFacts_3544_; lean_object* v_quantifiedFacts_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3563_; 
v_sortInfo_3541_ = lean_ctor_get(v_a_3525_, 0);
v_sortMap_3542_ = lean_ctor_get(v_a_3525_, 1);
v_predInfo_3543_ = lean_ctor_get(v_a_3525_, 2);
v_groundFacts_3544_ = lean_ctor_get(v_a_3525_, 3);
v_quantifiedFacts_3545_ = lean_ctor_get(v_a_3525_, 4);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_a_3525_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3547_ = v_a_3525_;
v_isShared_3548_ = v_isSharedCheck_3563_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_quantifiedFacts_3545_);
lean_inc(v_groundFacts_3544_);
lean_inc(v_predInfo_3543_);
lean_inc(v_sortMap_3542_);
lean_inc(v_sortInfo_3541_);
lean_dec(v_a_3525_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3563_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
lean_inc_ref(v_elements_3534_);
if (v_isShared_3537_ == 0)
{
v___x_3550_ = v___x_3536_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_type_3532_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_level_3533_);
lean_ctor_set(v_reuseFailAlloc_3562_, 2, v_elements_3534_);
v___x_3550_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3551_; lean_object* v___y_3553_; uint8_t v___x_3558_; 
lean_inc(v_key_3530_);
v___x_3551_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_registerSort_spec__0___redArg(v_sortInfo_3541_, v_key_3530_, v___x_3550_);
v___x_3558_ = lean_nat_dec_lt(v___x_3539_, v___x_3538_);
if (v___x_3558_ == 0)
{
lean_dec_ref(v_elements_3534_);
lean_dec(v_key_3530_);
v___y_3553_ = v_sortMap_3542_;
goto v___jp_3552_;
}
else
{
size_t v___x_3559_; size_t v___x_3560_; lean_object* v___x_3561_; 
v___x_3559_ = ((size_t)0ULL);
v___x_3560_ = lean_usize_of_nat(v___x_3538_);
v___x_3561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__4(v_key_3530_, v_elements_3534_, v___x_3559_, v___x_3560_, v_sortMap_3542_);
lean_dec_ref(v_elements_3534_);
v___y_3553_ = v___x_3561_;
goto v___jp_3552_;
}
v___jp_3552_:
{
lean_object* v___x_3555_; 
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 1, v___y_3553_);
lean_ctor_set(v___x_3547_, 0, v___x_3551_);
v___x_3555_ = v___x_3547_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v___y_3553_);
lean_ctor_set(v_reuseFailAlloc_3557_, 2, v_predInfo_3543_);
lean_ctor_set(v_reuseFailAlloc_3557_, 3, v_groundFacts_3544_);
lean_ctor_set(v_reuseFailAlloc_3557_, 4, v_quantifiedFacts_3545_);
v___x_3555_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
v_a_3524_ = v_tail_3531_;
v_a_3525_ = v___x_3555_;
goto _start;
}
}
}
}
}
else
{
lean_del_object(v___x_3536_);
lean_dec_ref(v_elements_3534_);
lean_dec(v_level_3533_);
lean_dec_ref(v_type_3532_);
lean_dec(v_key_3530_);
v_a_3524_ = v_tail_3531_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___redArg___boxed(lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___redArg(v_a_3566_, v_a_3567_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__6(lean_object* v_as_3570_, size_t v_sz_3571_, size_t v_i_3572_, lean_object* v_b_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
uint8_t v___x_3582_; 
v___x_3582_ = lean_usize_dec_lt(v_i_3572_, v_sz_3571_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; 
v___x_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3583_, 0, v_b_3573_);
return v___x_3583_;
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3585_; 
v_a_3584_ = lean_array_uget_borrowed(v_as_3570_, v_i_3572_);
lean_inc(v_a_3584_);
v___x_3585_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___redArg(v_a_3584_, v_b_3573_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3598_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3588_ = v___x_3585_;
v_isShared_3589_ = v_isSharedCheck_3598_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3585_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3598_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
if (lean_obj_tag(v_a_3586_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; 
v_a_3590_ = lean_ctor_get(v_a_3586_, 0);
lean_inc(v_a_3590_);
lean_dec_ref_known(v_a_3586_, 1);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 0, v_a_3590_);
v___x_3592_ = v___x_3588_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
else
{
lean_object* v_a_3594_; size_t v___x_3595_; size_t v___x_3596_; 
lean_del_object(v___x_3588_);
v_a_3594_ = lean_ctor_get(v_a_3586_, 0);
lean_inc(v_a_3594_);
lean_dec_ref_known(v_a_3586_, 1);
v___x_3595_ = ((size_t)1ULL);
v___x_3596_ = lean_usize_add(v_i_3572_, v___x_3595_);
v_i_3572_ = v___x_3596_;
v_b_3573_ = v_a_3594_;
goto _start;
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
v_a_3599_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3585_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3585_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__6___boxed(lean_object* v_as_3607_, lean_object* v_sz_3608_, lean_object* v_i_3609_, lean_object* v_b_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
size_t v_sz_boxed_3619_; size_t v_i_boxed_3620_; lean_object* v_res_3621_; 
v_sz_boxed_3619_ = lean_unbox_usize(v_sz_3608_);
lean_dec(v_sz_3608_);
v_i_boxed_3620_ = lean_unbox_usize(v_i_3609_);
lean_dec(v_i_3609_);
v_res_3621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__6(v_as_3607_, v_sz_boxed_3619_, v_i_boxed_3620_, v_b_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v_as_3607_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble(lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v_sorts_3632_; lean_object* v_preds_3633_; lean_object* v_groundFacts_3634_; lean_object* v_quantifiedFacts_3635_; lean_object* v_remainingHyps_3636_; lean_object* v_buckets_3637_; lean_object* v___x_3638_; size_t v_sz_3639_; size_t v___x_3640_; lean_object* v___x_3641_; 
v___x_3630_ = lean_st_ref_get(v_a_3622_);
v___x_3631_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__1);
v_sorts_3632_ = lean_ctor_get(v___x_3630_, 0);
lean_inc_ref(v_sorts_3632_);
v_preds_3633_ = lean_ctor_get(v___x_3630_, 4);
lean_inc_ref(v_preds_3633_);
v_groundFacts_3634_ = lean_ctor_get(v___x_3630_, 6);
lean_inc_ref(v_groundFacts_3634_);
v_quantifiedFacts_3635_ = lean_ctor_get(v___x_3630_, 7);
lean_inc_ref(v_quantifiedFacts_3635_);
v_remainingHyps_3636_ = lean_ctor_get(v___x_3630_, 8);
lean_inc_ref(v_remainingHyps_3636_);
lean_dec(v___x_3630_);
v_buckets_3637_ = lean_ctor_get(v_sorts_3632_, 1);
lean_inc_ref(v_buckets_3637_);
lean_dec_ref(v_sorts_3632_);
v___x_3638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3631_);
lean_ctor_set(v___x_3638_, 1, v___x_3631_);
lean_ctor_set(v___x_3638_, 2, v___x_3631_);
lean_ctor_set(v___x_3638_, 3, v_groundFacts_3634_);
lean_ctor_set(v___x_3638_, 4, v_quantifiedFacts_3635_);
v_sz_3639_ = lean_array_size(v_buckets_3637_);
v___x_3640_ = ((size_t)0ULL);
v___x_3641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__6(v_buckets_3637_, v_sz_3639_, v___x_3640_, v___x_3638_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_);
lean_dec_ref(v_buckets_3637_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v_buckets_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3668_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref_known(v___x_3641_, 1);
v_buckets_3643_ = lean_ctor_get(v_preds_3633_, 1);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_preds_3633_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; 
v_unused_3669_ = lean_ctor_get(v_preds_3633_, 0);
lean_dec(v_unused_3669_);
v___x_3645_ = v_preds_3633_;
v_isShared_3646_ = v_isSharedCheck_3668_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_buckets_3643_);
lean_dec(v_preds_3633_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3668_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
size_t v_sz_3647_; lean_object* v___x_3648_; 
v_sz_3647_ = lean_array_size(v_buckets_3643_);
v___x_3648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__7(v_buckets_3643_, v_sz_3647_, v___x_3640_, v_a_3642_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_);
lean_dec_ref(v_buckets_3643_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3659_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3651_ = v___x_3648_;
v_isShared_3652_ = v_isSharedCheck_3659_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3648_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3659_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 1, v_remainingHyps_3636_);
lean_ctor_set(v___x_3645_, 0, v_a_3649_);
v___x_3654_ = v___x_3645_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3649_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_remainingHyps_3636_);
v___x_3654_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3656_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v___x_3654_);
v___x_3656_ = v___x_3651_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_del_object(v___x_3645_);
lean_dec_ref(v_remainingHyps_3636_);
v_a_3660_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3648_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3648_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec_ref(v_remainingHyps_3636_);
lean_dec_ref(v_preds_3633_);
v_a_3670_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3641_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3641_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble___boxed(lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble(v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
lean_dec(v_a_3680_);
lean_dec_ref(v_a_3679_);
lean_dec(v_a_3678_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0(lean_object* v_00_u03b2_3687_, lean_object* v_m_3688_, lean_object* v_a_3689_, lean_object* v_b_3690_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0___redArg(v_m_3688_, v_a_3689_, v_b_3690_);
return v___x_3691_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1(lean_object* v_00_u03b2_3692_, lean_object* v_m_3693_, lean_object* v_a_3694_){
_start:
{
uint8_t v___x_3695_; 
v___x_3695_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___redArg(v_m_3693_, v_a_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1___boxed(lean_object* v_00_u03b2_3696_, lean_object* v_m_3697_, lean_object* v_a_3698_){
_start:
{
uint8_t v_res_3699_; lean_object* v_r_3700_; 
v_res_3699_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__1(v_00_u03b2_3696_, v_m_3697_, v_a_3698_);
lean_dec(v_a_3698_);
lean_dec_ref(v_m_3697_);
v_r_3700_ = lean_box(v_res_3699_);
return v_r_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3(lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___redArg(v_a_3701_, v_a_3702_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3___boxed(lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__3(v_a_3712_, v_a_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5(lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___redArg(v_a_3723_, v_a_3724_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5___boxed(lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__5(v_a_3734_, v_a_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
return v_res_3744_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0(lean_object* v_00_u03b2_3745_, lean_object* v_a_3746_, lean_object* v_x_3747_){
_start:
{
uint8_t v___x_3748_; 
v___x_3748_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___redArg(v_a_3746_, v_x_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3749_, lean_object* v_a_3750_, lean_object* v_x_3751_){
_start:
{
uint8_t v_res_3752_; lean_object* v_r_3753_; 
v_res_3752_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__0(v_00_u03b2_3749_, v_a_3750_, v_x_3751_);
lean_dec(v_x_3751_);
lean_dec_ref(v_a_3750_);
v_r_3753_ = lean_box(v_res_3752_);
return v_r_3753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1(lean_object* v_00_u03b2_3754_, lean_object* v_data_3755_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1___redArg(v_data_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__2(lean_object* v_00_u03b2_3757_, lean_object* v_a_3758_, lean_object* v_b_3759_, lean_object* v_x_3760_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__2___redArg(v_a_3758_, v_b_3759_, v_x_3760_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3762_, lean_object* v_i_3763_, lean_object* v_source_3764_, lean_object* v_target_3765_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2___redArg(v_i_3763_, v_source_3764_, v_target_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2_spec__10(lean_object* v_00_u03b2_3767_, lean_object* v_x_3768_, lean_object* v_x_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble_spec__0_spec__1_spec__2_spec__10___redArg(v_x_3768_, v_x_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2_spec__6(lean_object* v_as_3771_, size_t v_i_3772_, size_t v_stop_3773_, lean_object* v_b_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v_a_3784_; uint8_t v___x_3788_; 
v___x_3788_ = lean_usize_dec_eq(v_i_3772_, v_stop_3773_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; 
v___x_3789_ = lean_array_uget_borrowed(v_as_3771_, v_i_3772_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v___x_3790_; 
v___x_3790_ = lean_box(0);
v_a_3784_ = v___x_3790_;
goto v___jp_3783_;
}
else
{
lean_object* v_val_3791_; lean_object* v___x_3792_; 
v_val_3791_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_val_3791_);
v___x_3792_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processLocalDecl(v_val_3791_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v_a_3784_ = v_a_3793_;
goto v___jp_3783_;
}
else
{
return v___x_3792_;
}
}
}
else
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3794_, 0, v_b_3774_);
return v___x_3794_;
}
v___jp_3783_:
{
size_t v___x_3785_; size_t v___x_3786_; 
v___x_3785_ = ((size_t)1ULL);
v___x_3786_ = lean_usize_add(v_i_3772_, v___x_3785_);
v_i_3772_ = v___x_3786_;
v_b_3774_ = v_a_3784_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_as_3795_, lean_object* v_i_3796_, lean_object* v_stop_3797_, lean_object* v_b_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
size_t v_i_boxed_3807_; size_t v_stop_boxed_3808_; lean_object* v_res_3809_; 
v_i_boxed_3807_ = lean_unbox_usize(v_i_3796_);
lean_dec(v_i_3796_);
v_stop_boxed_3808_ = lean_unbox_usize(v_stop_3797_);
lean_dec(v_stop_3797_);
v_res_3809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2_spec__6(v_as_3795_, v_i_boxed_3807_, v_stop_boxed_3808_, v_b_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v_as_3795_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(lean_object* v_as_3810_, size_t v_i_3811_, size_t v_stop_3812_, lean_object* v_b_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v_a_3823_; uint8_t v___x_3827_; 
v___x_3827_ = lean_usize_dec_eq(v_i_3811_, v_stop_3812_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_array_uget_borrowed(v_as_3810_, v_i_3811_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v___x_3829_; 
v___x_3829_ = lean_box(0);
v_a_3823_ = v___x_3829_;
goto v___jp_3822_;
}
else
{
lean_object* v_val_3830_; lean_object* v___x_3831_; 
v_val_3830_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_val_3830_);
v___x_3831_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processLocalDecl(v_val_3830_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref_known(v___x_3831_, 1);
v_a_3823_ = v_a_3832_;
goto v___jp_3822_;
}
else
{
return v___x_3831_;
}
}
}
else
{
lean_object* v___x_3833_; 
v___x_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3833_, 0, v_b_3813_);
return v___x_3833_;
}
v___jp_3822_:
{
size_t v___x_3824_; size_t v___x_3825_; lean_object* v___x_3826_; 
v___x_3824_ = ((size_t)1ULL);
v___x_3825_ = lean_usize_add(v_i_3811_, v___x_3824_);
v___x_3826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2_spec__6(v_as_3810_, v___x_3825_, v_stop_3812_, v_a_3823_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
return v___x_3826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3834_, lean_object* v_i_3835_, lean_object* v_stop_3836_, lean_object* v_b_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
size_t v_i_boxed_3846_; size_t v_stop_boxed_3847_; lean_object* v_res_3848_; 
v_i_boxed_3846_ = lean_unbox_usize(v_i_3835_);
lean_dec(v_i_3835_);
v_stop_boxed_3847_ = lean_unbox_usize(v_stop_3836_);
lean_dec(v_stop_3836_);
v_res_3848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(v_as_3834_, v_i_boxed_3846_, v_stop_boxed_3847_, v_b_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v_as_3834_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
if (lean_obj_tag(v_x_3849_) == 0)
{
lean_object* v_cs_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3872_; 
v_cs_3858_ = lean_ctor_get(v_x_3849_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_x_3849_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3860_ = v_x_3849_;
v_isShared_3861_ = v_isSharedCheck_3872_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_cs_3858_);
lean_dec(v_x_3849_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3872_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; uint8_t v___x_3865_; 
v___x_3862_ = lean_unsigned_to_nat(0u);
v___x_3863_ = lean_array_get_size(v_cs_3858_);
v___x_3864_ = lean_box(0);
v___x_3865_ = lean_nat_dec_lt(v___x_3862_, v___x_3863_);
if (v___x_3865_ == 0)
{
lean_object* v___x_3867_; 
lean_dec_ref(v_cs_3858_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3864_);
v___x_3867_ = v___x_3860_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3864_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
else
{
size_t v___x_3869_; size_t v___x_3870_; lean_object* v___x_3871_; 
lean_del_object(v___x_3860_);
v___x_3869_ = ((size_t)0ULL);
v___x_3870_ = lean_usize_of_nat(v___x_3863_);
v___x_3871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__4(v_cs_3858_, v___x_3869_, v___x_3870_, v___x_3864_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec_ref(v_cs_3858_);
return v___x_3871_;
}
}
}
else
{
lean_object* v_vs_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3887_; 
v_vs_3873_ = lean_ctor_get(v_x_3849_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_x_3849_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3875_ = v_x_3849_;
v_isShared_3876_ = v_isSharedCheck_3887_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_vs_3873_);
lean_dec(v_x_3849_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3887_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; uint8_t v___x_3880_; 
v___x_3877_ = lean_unsigned_to_nat(0u);
v___x_3878_ = lean_array_get_size(v_vs_3873_);
v___x_3879_ = lean_box(0);
v___x_3880_ = lean_nat_dec_lt(v___x_3877_, v___x_3878_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3882_; 
lean_dec_ref(v_vs_3873_);
if (v_isShared_3876_ == 0)
{
lean_ctor_set_tag(v___x_3875_, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3879_);
v___x_3882_ = v___x_3875_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3879_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
else
{
size_t v___x_3884_; size_t v___x_3885_; lean_object* v___x_3886_; 
lean_del_object(v___x_3875_);
v___x_3884_ = ((size_t)0ULL);
v___x_3885_ = lean_usize_of_nat(v___x_3878_);
v___x_3886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(v_vs_3873_, v___x_3884_, v___x_3885_, v___x_3879_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec_ref(v_vs_3873_);
return v___x_3886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__4(lean_object* v_as_3888_, size_t v_i_3889_, size_t v_stop_3890_, lean_object* v_b_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
uint8_t v___x_3900_; 
v___x_3900_ = lean_usize_dec_eq(v_i_3889_, v_stop_3890_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = lean_array_uget_borrowed(v_as_3888_, v_i_3889_);
lean_inc(v___x_3901_);
v___x_3902_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__3(v___x_3901_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; size_t v___x_3904_; size_t v___x_3905_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref_known(v___x_3902_, 1);
v___x_3904_ = ((size_t)1ULL);
v___x_3905_ = lean_usize_add(v_i_3889_, v___x_3904_);
v_i_3889_ = v___x_3905_;
v_b_3891_ = v_a_3903_;
goto _start;
}
else
{
return v___x_3902_;
}
}
else
{
lean_object* v___x_3907_; 
v___x_3907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3907_, 0, v_b_3891_);
return v___x_3907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3908_, lean_object* v_i_3909_, lean_object* v_stop_3910_, lean_object* v_b_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
size_t v_i_boxed_3920_; size_t v_stop_boxed_3921_; lean_object* v_res_3922_; 
v_i_boxed_3920_ = lean_unbox_usize(v_i_3909_);
lean_dec(v_i_3909_);
v_stop_boxed_3921_ = lean_unbox_usize(v_stop_3910_);
lean_dec(v_stop_3910_);
v_res_3922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__4(v_as_3908_, v_i_boxed_3920_, v_stop_boxed_3921_, v_b_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v_as_3908_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__3(v_x_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__3(lean_object* v_t_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v_root_3942_; lean_object* v_tail_3943_; lean_object* v___x_3944_; 
v_root_3942_ = lean_ctor_get(v_t_3933_, 0);
lean_inc_ref(v_root_3942_);
v_tail_3943_ = lean_ctor_get(v_t_3933_, 1);
lean_inc_ref(v_tail_3943_);
lean_dec_ref(v_t_3933_);
v___x_3944_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__3(v_root_3942_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3958_; 
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3958_ == 0)
{
lean_object* v_unused_3959_; 
v_unused_3959_ = lean_ctor_get(v___x_3944_, 0);
lean_dec(v_unused_3959_);
v___x_3946_ = v___x_3944_;
v_isShared_3947_ = v_isSharedCheck_3958_;
goto v_resetjp_3945_;
}
else
{
lean_dec(v___x_3944_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3958_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; uint8_t v___x_3951_; 
v___x_3948_ = lean_unsigned_to_nat(0u);
v___x_3949_ = lean_array_get_size(v_tail_3943_);
v___x_3950_ = lean_box(0);
v___x_3951_ = lean_nat_dec_lt(v___x_3948_, v___x_3949_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3953_; 
lean_dec_ref(v_tail_3943_);
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 0, v___x_3950_);
v___x_3953_ = v___x_3946_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3950_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
else
{
size_t v___x_3955_; size_t v___x_3956_; lean_object* v___x_3957_; 
lean_del_object(v___x_3946_);
v___x_3955_ = ((size_t)0ULL);
v___x_3956_ = lean_usize_of_nat(v___x_3949_);
v___x_3957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(v_tail_3943_, v___x_3955_, v___x_3956_, v___x_3950_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
lean_dec_ref(v_tail_3943_);
return v___x_3957_;
}
}
}
else
{
lean_dec_ref(v_tail_3943_);
return v___x_3944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__3___boxed(lean_object* v_t_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__3(v_t_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
lean_dec(v___y_3961_);
return v_res_3969_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1(lean_object* v_x_3971_, size_t v_x_3972_, size_t v_x_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
if (lean_obj_tag(v_x_3971_) == 0)
{
lean_object* v_cs_3982_; lean_object* v___x_3983_; size_t v___x_3984_; lean_object* v_j_3985_; lean_object* v___x_3986_; size_t v___x_3987_; size_t v___x_3988_; size_t v___x_3989_; size_t v___x_3990_; size_t v___x_3991_; size_t v___x_3992_; lean_object* v___x_3993_; 
v_cs_3982_ = lean_ctor_get(v_x_3971_, 0);
lean_inc_ref(v_cs_3982_);
lean_dec_ref_known(v_x_3971_, 1);
v___x_3983_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1___closed__0);
v___x_3984_ = lean_usize_shift_right(v_x_3972_, v_x_3973_);
v_j_3985_ = lean_usize_to_nat(v___x_3984_);
v___x_3986_ = lean_array_get_borrowed(v___x_3983_, v_cs_3982_, v_j_3985_);
v___x_3987_ = ((size_t)1ULL);
v___x_3988_ = lean_usize_shift_left(v___x_3987_, v_x_3973_);
v___x_3989_ = lean_usize_sub(v___x_3988_, v___x_3987_);
v___x_3990_ = lean_usize_land(v_x_3972_, v___x_3989_);
v___x_3991_ = ((size_t)5ULL);
v___x_3992_ = lean_usize_sub(v_x_3973_, v___x_3991_);
lean_inc(v___x_3986_);
v___x_3993_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1(v___x_3986_, v___x_3990_, v___x_3992_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4008_; 
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4008_ == 0)
{
lean_object* v_unused_4009_; 
v_unused_4009_ = lean_ctor_get(v___x_3993_, 0);
lean_dec(v_unused_4009_);
v___x_3995_ = v___x_3993_;
v_isShared_3996_ = v_isSharedCheck_4008_;
goto v_resetjp_3994_;
}
else
{
lean_dec(v___x_3993_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4008_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; uint8_t v___x_4001_; 
v___x_3997_ = lean_unsigned_to_nat(1u);
v___x_3998_ = lean_nat_add(v_j_3985_, v___x_3997_);
lean_dec(v_j_3985_);
v___x_3999_ = lean_array_get_size(v_cs_3982_);
v___x_4000_ = lean_box(0);
v___x_4001_ = lean_nat_dec_lt(v___x_3998_, v___x_3999_);
if (v___x_4001_ == 0)
{
lean_object* v___x_4003_; 
lean_dec(v___x_3998_);
lean_dec_ref(v_cs_3982_);
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 0, v___x_4000_);
v___x_4003_ = v___x_3995_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_4000_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
else
{
size_t v___x_4005_; size_t v___x_4006_; lean_object* v___x_4007_; 
lean_del_object(v___x_3995_);
v___x_4005_ = lean_usize_of_nat(v___x_3998_);
lean_dec(v___x_3998_);
v___x_4006_ = lean_usize_of_nat(v___x_3999_);
v___x_4007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1_spec__4(v_cs_3982_, v___x_4005_, v___x_4006_, v___x_4000_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
lean_dec_ref(v_cs_3982_);
return v___x_4007_;
}
}
}
else
{
lean_dec(v_j_3985_);
lean_dec_ref(v_cs_3982_);
return v___x_3993_;
}
}
else
{
lean_object* v_vs_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4024_; 
v_vs_4010_ = lean_ctor_get(v_x_3971_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v_x_3971_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4012_ = v_x_3971_;
v_isShared_4013_ = v_isSharedCheck_4024_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_vs_4010_);
lean_dec(v_x_3971_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4024_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; uint8_t v___x_4017_; 
v___x_4014_ = lean_usize_to_nat(v_x_3972_);
v___x_4015_ = lean_array_get_size(v_vs_4010_);
v___x_4016_ = lean_box(0);
v___x_4017_ = lean_nat_dec_lt(v___x_4014_, v___x_4015_);
if (v___x_4017_ == 0)
{
lean_object* v___x_4019_; 
lean_dec(v___x_4014_);
lean_dec_ref(v_vs_4010_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set_tag(v___x_4012_, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4016_);
v___x_4019_ = v___x_4012_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v___x_4016_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
else
{
size_t v___x_4021_; size_t v___x_4022_; lean_object* v___x_4023_; 
lean_del_object(v___x_4012_);
v___x_4021_ = lean_usize_of_nat(v___x_4014_);
lean_dec(v___x_4014_);
v___x_4022_ = lean_usize_of_nat(v___x_4015_);
v___x_4023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(v_vs_4010_, v___x_4021_, v___x_4022_, v___x_4016_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
lean_dec_ref(v_vs_4010_);
return v___x_4023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1___boxed(lean_object* v_x_4025_, lean_object* v_x_4026_, lean_object* v_x_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
size_t v_x_8747__boxed_4036_; size_t v_x_8748__boxed_4037_; lean_object* v_res_4038_; 
v_x_8747__boxed_4036_ = lean_unbox_usize(v_x_4026_);
lean_dec(v_x_4026_);
v_x_8748__boxed_4037_ = lean_unbox_usize(v_x_4027_);
lean_dec(v_x_4027_);
v_res_4038_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1(v_x_4025_, v_x_8747__boxed_4036_, v_x_8748__boxed_4037_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0(lean_object* v_t_4039_, lean_object* v_start_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v___x_4049_; uint8_t v___x_4050_; 
v___x_4049_ = lean_unsigned_to_nat(0u);
v___x_4050_ = lean_nat_dec_eq(v_start_4040_, v___x_4049_);
if (v___x_4050_ == 0)
{
lean_object* v_root_4051_; lean_object* v_tail_4052_; size_t v_shift_4053_; lean_object* v_tailOff_4054_; uint8_t v___x_4055_; 
v_root_4051_ = lean_ctor_get(v_t_4039_, 0);
lean_inc_ref(v_root_4051_);
v_tail_4052_ = lean_ctor_get(v_t_4039_, 1);
lean_inc_ref(v_tail_4052_);
v_shift_4053_ = lean_ctor_get_usize(v_t_4039_, 4);
v_tailOff_4054_ = lean_ctor_get(v_t_4039_, 3);
lean_inc(v_tailOff_4054_);
lean_dec_ref(v_t_4039_);
v___x_4055_ = lean_nat_dec_le(v_tailOff_4054_, v_start_4040_);
if (v___x_4055_ == 0)
{
size_t v___x_4056_; lean_object* v___x_4057_; 
lean_dec(v_tailOff_4054_);
v___x_4056_ = lean_usize_of_nat(v_start_4040_);
v___x_4057_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__1(v_root_4051_, v___x_4056_, v_shift_4053_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4070_; 
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4070_ == 0)
{
lean_object* v_unused_4071_; 
v_unused_4071_ = lean_ctor_get(v___x_4057_, 0);
lean_dec(v_unused_4071_);
v___x_4059_ = v___x_4057_;
v_isShared_4060_ = v_isSharedCheck_4070_;
goto v_resetjp_4058_;
}
else
{
lean_dec(v___x_4057_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4070_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; uint8_t v___x_4063_; 
v___x_4061_ = lean_array_get_size(v_tail_4052_);
v___x_4062_ = lean_box(0);
v___x_4063_ = lean_nat_dec_lt(v___x_4049_, v___x_4061_);
if (v___x_4063_ == 0)
{
lean_object* v___x_4065_; 
lean_dec_ref(v_tail_4052_);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 0, v___x_4062_);
v___x_4065_ = v___x_4059_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4062_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
else
{
size_t v___x_4067_; size_t v___x_4068_; lean_object* v___x_4069_; 
lean_del_object(v___x_4059_);
v___x_4067_ = ((size_t)0ULL);
v___x_4068_ = lean_usize_of_nat(v___x_4061_);
v___x_4069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(v_tail_4052_, v___x_4067_, v___x_4068_, v___x_4062_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
lean_dec_ref(v_tail_4052_);
return v___x_4069_;
}
}
}
else
{
lean_dec_ref(v_tail_4052_);
return v___x_4057_;
}
}
else
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; uint8_t v___x_4075_; 
lean_dec_ref(v_root_4051_);
v___x_4072_ = lean_nat_sub(v_start_4040_, v_tailOff_4054_);
lean_dec(v_tailOff_4054_);
v___x_4073_ = lean_array_get_size(v_tail_4052_);
v___x_4074_ = lean_box(0);
v___x_4075_ = lean_nat_dec_lt(v___x_4072_, v___x_4073_);
if (v___x_4075_ == 0)
{
lean_object* v___x_4076_; 
lean_dec(v___x_4072_);
lean_dec_ref(v_tail_4052_);
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4074_);
return v___x_4076_;
}
else
{
size_t v___x_4077_; size_t v___x_4078_; lean_object* v___x_4079_; 
v___x_4077_ = lean_usize_of_nat(v___x_4072_);
lean_dec(v___x_4072_);
v___x_4078_ = lean_usize_of_nat(v___x_4073_);
v___x_4079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__2(v_tail_4052_, v___x_4077_, v___x_4078_, v___x_4074_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
lean_dec_ref(v_tail_4052_);
return v___x_4079_;
}
}
}
else
{
lean_object* v___x_4080_; 
v___x_4080_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0_spec__3(v_t_4039_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
return v___x_4080_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0___boxed(lean_object* v_t_4081_, lean_object* v_start_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0(v_t_4081_, v_start_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec(v_start_4082_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0(lean_object* v_lctx_4092_, lean_object* v_start_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v_decls_4102_; lean_object* v___x_4103_; 
v_decls_4102_ = lean_ctor_get(v_lctx_4092_, 1);
lean_inc_ref(v_decls_4102_);
lean_dec_ref(v_lctx_4092_);
v___x_4103_ = l_Lean_PersistentArray_forM___at___00Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0_spec__0(v_decls_4102_, v_start_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0___boxed(lean_object* v_lctx_4104_, lean_object* v_start_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = l_Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0(v_lctx_4104_, v_start_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec(v_start_4105_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__1(lean_object* v_as_4115_, size_t v_i_4116_, size_t v_stop_4117_, lean_object* v_b_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
uint8_t v___x_4127_; 
v___x_4127_ = lean_usize_dec_eq(v_i_4116_, v_stop_4117_);
if (v___x_4127_ == 0)
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4128_ = lean_array_uget_borrowed(v_as_4115_, v_i_4116_);
lean_inc(v___x_4128_);
v___x_4129_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_processHyp(v___x_4128_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v_a_4130_; size_t v___x_4131_; size_t v___x_4132_; 
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc(v_a_4130_);
lean_dec_ref_known(v___x_4129_, 1);
v___x_4131_ = ((size_t)1ULL);
v___x_4132_ = lean_usize_add(v_i_4116_, v___x_4131_);
v_i_4116_ = v___x_4132_;
v_b_4118_ = v_a_4130_;
goto _start;
}
else
{
return v___x_4129_;
}
}
else
{
lean_object* v___x_4134_; 
v___x_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4134_, 0, v_b_4118_);
return v___x_4134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__1___boxed(lean_object* v_as_4135_, lean_object* v_i_4136_, lean_object* v_stop_4137_, lean_object* v_b_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
size_t v_i_boxed_4147_; size_t v_stop_boxed_4148_; lean_object* v_res_4149_; 
v_i_boxed_4147_ = lean_unbox_usize(v_i_4136_);
lean_dec(v_i_4136_);
v_stop_boxed_4148_ = lean_unbox_usize(v_stop_4137_);
lean_dec(v_stop_4137_);
v_res_4149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__1(v_as_4135_, v_i_boxed_4147_, v_stop_boxed_4148_, v_b_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v___y_4139_);
lean_dec_ref(v_as_4135_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem(lean_object* v_hyps_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_){
_start:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v_lctx_4181_; lean_object* v___x_4182_; 
v___x_4158_ = lean_unsigned_to_nat(0u);
v___x_4159_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_run___redArg___closed__3);
v___x_4160_ = lean_st_mk_ref(v___x_4159_);
v_lctx_4181_ = lean_ctor_get(v_a_4153_, 2);
lean_inc_ref(v_lctx_4181_);
v___x_4182_ = l_Lean_LocalContext_forM___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__0(v_lctx_4181_, v___x_4158_, v___x_4160_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v___x_4183_; 
lean_dec_ref_known(v___x_4182_, 1);
v___x_4183_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_ensureHasElement(v___x_4160_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v___x_4184_; uint8_t v___x_4185_; 
lean_dec_ref_known(v___x_4183_, 1);
v___x_4184_ = lean_array_get_size(v_hyps_4150_);
v___x_4185_ = lean_nat_dec_lt(v___x_4158_, v___x_4184_);
if (v___x_4185_ == 0)
{
goto v___jp_4161_;
}
else
{
lean_object* v___x_4186_; size_t v___x_4187_; size_t v___x_4188_; lean_object* v___x_4189_; 
v___x_4186_ = lean_box(0);
v___x_4187_ = ((size_t)0ULL);
v___x_4188_ = lean_usize_of_nat(v___x_4184_);
v___x_4189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem_spec__1(v_hyps_4150_, v___x_4187_, v___x_4188_, v___x_4186_, v___x_4160_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_dec_ref_known(v___x_4189_, 1);
goto v___jp_4161_;
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
lean_dec(v___x_4160_);
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4189_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4189_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_dec(v___x_4160_);
v_a_4198_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4183_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4183_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec(v___x_4160_);
v_a_4206_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4182_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4182_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
v___jp_4161_:
{
lean_object* v___x_4162_; 
v___x_4162_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_pruneUnusedElements(v___x_4160_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v___x_4163_; 
lean_dec_ref_known(v___x_4162_, 1);
v___x_4163_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_assemble(v___x_4160_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4172_; 
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4166_ = v___x_4163_;
v_isShared_4167_ = v_isSharedCheck_4172_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4163_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4172_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4168_; lean_object* v___x_4170_; 
v___x_4168_ = lean_st_ref_get(v___x_4160_);
lean_dec(v___x_4160_);
lean_dec(v___x_4168_);
if (v_isShared_4167_ == 0)
{
v___x_4170_ = v___x_4166_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4164_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
else
{
lean_dec(v___x_4160_);
return v___x_4163_;
}
}
else
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4180_; 
lean_dec(v___x_4160_);
v_a_4173_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4175_ = v___x_4162_;
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4162_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4178_; 
if (v_isShared_4176_ == 0)
{
v___x_4178_ = v___x_4175_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem___boxed(lean_object* v_hyps_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem(v_hyps_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
lean_dec(v_a_4220_);
lean_dec_ref(v_a_4219_);
lean_dec(v_a_4218_);
lean_dec_ref(v_a_4217_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec_ref(v_hyps_4214_);
return v_res_4222_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4223_ = lean_unsigned_to_nat(32u);
v___x_4224_ = lean_mk_empty_array_with_capacity(v___x_4223_);
v___x_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4224_);
return v___x_4225_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__1(void){
_start:
{
size_t v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4226_ = ((size_t)5ULL);
v___x_4227_ = lean_unsigned_to_nat(0u);
v___x_4228_ = lean_unsigned_to_nat(32u);
v___x_4229_ = lean_mk_empty_array_with_capacity(v___x_4228_);
v___x_4230_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__0);
v___x_4231_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4231_, 0, v___x_4230_);
lean_ctor_set(v___x_4231_, 1, v___x_4229_);
lean_ctor_set(v___x_4231_, 2, v___x_4227_);
lean_ctor_set(v___x_4231_, 3, v___x_4227_);
lean_ctor_set_usize(v___x_4231_, 4, v___x_4226_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg(lean_object* v___y_4232_){
_start:
{
lean_object* v___x_4234_; lean_object* v_traceState_4235_; lean_object* v_traces_4236_; lean_object* v___x_4237_; lean_object* v_traceState_4238_; lean_object* v_env_4239_; lean_object* v_nextMacroScope_4240_; lean_object* v_ngen_4241_; lean_object* v_auxDeclNGen_4242_; lean_object* v_cache_4243_; lean_object* v_recordedDeps_4244_; lean_object* v_messages_4245_; lean_object* v_infoState_4246_; lean_object* v_snapshotTasks_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4266_; 
v___x_4234_ = lean_st_ref_get(v___y_4232_);
v_traceState_4235_ = lean_ctor_get(v___x_4234_, 4);
lean_inc_ref(v_traceState_4235_);
lean_dec(v___x_4234_);
v_traces_4236_ = lean_ctor_get(v_traceState_4235_, 0);
lean_inc_ref(v_traces_4236_);
lean_dec_ref(v_traceState_4235_);
v___x_4237_ = lean_st_ref_take(v___y_4232_);
v_traceState_4238_ = lean_ctor_get(v___x_4237_, 4);
v_env_4239_ = lean_ctor_get(v___x_4237_, 0);
v_nextMacroScope_4240_ = lean_ctor_get(v___x_4237_, 1);
v_ngen_4241_ = lean_ctor_get(v___x_4237_, 2);
v_auxDeclNGen_4242_ = lean_ctor_get(v___x_4237_, 3);
v_cache_4243_ = lean_ctor_get(v___x_4237_, 5);
v_recordedDeps_4244_ = lean_ctor_get(v___x_4237_, 6);
v_messages_4245_ = lean_ctor_get(v___x_4237_, 7);
v_infoState_4246_ = lean_ctor_get(v___x_4237_, 8);
v_snapshotTasks_4247_ = lean_ctor_get(v___x_4237_, 9);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4249_ = v___x_4237_;
v_isShared_4250_ = v_isSharedCheck_4266_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_snapshotTasks_4247_);
lean_inc(v_infoState_4246_);
lean_inc(v_messages_4245_);
lean_inc(v_recordedDeps_4244_);
lean_inc(v_cache_4243_);
lean_inc(v_traceState_4238_);
lean_inc(v_auxDeclNGen_4242_);
lean_inc(v_ngen_4241_);
lean_inc(v_nextMacroScope_4240_);
lean_inc(v_env_4239_);
lean_dec(v___x_4237_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4266_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
uint64_t v_tid_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4264_; 
v_tid_4251_ = lean_ctor_get_uint64(v_traceState_4238_, sizeof(void*)*1);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_traceState_4238_);
if (v_isSharedCheck_4264_ == 0)
{
lean_object* v_unused_4265_; 
v_unused_4265_ = lean_ctor_get(v_traceState_4238_, 0);
lean_dec(v_unused_4265_);
v___x_4253_ = v_traceState_4238_;
v_isShared_4254_ = v_isSharedCheck_4264_;
goto v_resetjp_4252_;
}
else
{
lean_dec(v_traceState_4238_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4264_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4255_; lean_object* v___x_4257_; 
v___x_4255_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___closed__1);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 0, v___x_4255_);
v___x_4257_ = v___x_4253_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4255_);
lean_ctor_set_uint64(v_reuseFailAlloc_4263_, sizeof(void*)*1, v_tid_4251_);
v___x_4257_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
lean_object* v___x_4259_; 
if (v_isShared_4250_ == 0)
{
lean_ctor_set(v___x_4249_, 4, v___x_4257_);
v___x_4259_ = v___x_4249_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_env_4239_);
lean_ctor_set(v_reuseFailAlloc_4262_, 1, v_nextMacroScope_4240_);
lean_ctor_set(v_reuseFailAlloc_4262_, 2, v_ngen_4241_);
lean_ctor_set(v_reuseFailAlloc_4262_, 3, v_auxDeclNGen_4242_);
lean_ctor_set(v_reuseFailAlloc_4262_, 4, v___x_4257_);
lean_ctor_set(v_reuseFailAlloc_4262_, 5, v_cache_4243_);
lean_ctor_set(v_reuseFailAlloc_4262_, 6, v_recordedDeps_4244_);
lean_ctor_set(v_reuseFailAlloc_4262_, 7, v_messages_4245_);
lean_ctor_set(v_reuseFailAlloc_4262_, 8, v_infoState_4246_);
lean_ctor_set(v_reuseFailAlloc_4262_, 9, v_snapshotTasks_4247_);
v___x_4259_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4260_ = lean_st_ref_put(v___y_4232_, v___x_4259_);
v___x_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4261_, 0, v_traces_4236_);
return v___x_4261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg___boxed(lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg(v___y_4267_);
lean_dec(v___y_4267_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14(lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg(v___y_4273_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___boxed(lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14(v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
return v_res_4281_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15(lean_object* v_opts_4282_, lean_object* v_opt_4283_){
_start:
{
lean_object* v_name_4284_; lean_object* v_defValue_4285_; lean_object* v_map_4286_; lean_object* v___x_4287_; 
v_name_4284_ = lean_ctor_get(v_opt_4283_, 0);
v_defValue_4285_ = lean_ctor_get(v_opt_4283_, 1);
v_map_4286_ = lean_ctor_get(v_opts_4282_, 0);
v___x_4287_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4286_, v_name_4284_);
if (lean_obj_tag(v___x_4287_) == 0)
{
uint8_t v___x_4288_; 
v___x_4288_ = lean_unbox(v_defValue_4285_);
return v___x_4288_;
}
else
{
lean_object* v_val_4289_; 
v_val_4289_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_val_4289_);
lean_dec_ref_known(v___x_4287_, 1);
if (lean_obj_tag(v_val_4289_) == 1)
{
uint8_t v_v_4290_; 
v_v_4290_ = lean_ctor_get_uint8(v_val_4289_, 0);
lean_dec_ref_known(v_val_4289_, 0);
return v_v_4290_;
}
else
{
uint8_t v___x_4291_; 
lean_dec(v_val_4289_);
v___x_4291_ = lean_unbox(v_defValue_4285_);
return v___x_4291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15___boxed(lean_object* v_opts_4292_, lean_object* v_opt_4293_){
_start:
{
uint8_t v_res_4294_; lean_object* v_r_4295_; 
v_res_4294_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15(v_opts_4292_, v_opt_4293_);
lean_dec_ref(v_opt_4293_);
lean_dec_ref(v_opts_4292_);
v_r_4295_ = lean_box(v_res_4294_);
return v_r_4295_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__0));
v___x_4298_ = l_Lean_stringToMessageData(v___x_4297_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0(lean_object* v_x_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4305_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___closed__1);
v___x_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0___boxed(lean_object* v_x_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___lam__0(v_x_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec_ref(v_x_4307_);
return v_res_4313_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_4317_; lean_object* v___x_4318_; 
v___x_4317_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__1));
v___x_4318_ = l_Lean_MessageData_ofFormat(v___x_4317_);
return v___x_4318_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__3(void){
_start:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4319_ = lean_box(1);
v___x_4320_ = l_Lean_MessageData_ofFormat(v___x_4319_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2(lean_object* v_a_4321_, lean_object* v_a_4322_){
_start:
{
if (lean_obj_tag(v_a_4321_) == 0)
{
lean_object* v___x_4323_; 
v___x_4323_ = l_List_reverse___redArg(v_a_4322_);
return v___x_4323_;
}
else
{
lean_object* v_head_4324_; lean_object* v_tail_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4351_; 
v_head_4324_ = lean_ctor_get(v_a_4321_, 0);
v_tail_4325_ = lean_ctor_get(v_a_4321_, 1);
v_isSharedCheck_4351_ = !lean_is_exclusive(v_a_4321_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4327_ = v_a_4321_;
v_isShared_4328_ = v_isSharedCheck_4351_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_tail_4325_);
lean_inc(v_head_4324_);
lean_dec(v_a_4321_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4351_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v_fst_4329_; lean_object* v_snd_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4350_; 
v_fst_4329_ = lean_ctor_get(v_head_4324_, 0);
v_snd_4330_ = lean_ctor_get(v_head_4324_, 1);
v_isSharedCheck_4350_ = !lean_is_exclusive(v_head_4324_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4332_ = v_head_4324_;
v_isShared_4333_ = v_isSharedCheck_4350_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_snd_4330_);
lean_inc(v_fst_4329_);
lean_dec(v_head_4324_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4350_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4339_; 
v___x_4334_ = l_Nat_reprFast(v_fst_4329_);
v___x_4335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4334_);
v___x_4336_ = l_Lean_MessageData_ofFormat(v___x_4335_);
v___x_4337_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__2);
if (v_isShared_4333_ == 0)
{
lean_ctor_set_tag(v___x_4332_, 7);
lean_ctor_set(v___x_4332_, 1, v___x_4337_);
lean_ctor_set(v___x_4332_, 0, v___x_4336_);
v___x_4339_ = v___x_4332_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v___x_4336_);
lean_ctor_set(v_reuseFailAlloc_4349_, 1, v___x_4337_);
v___x_4339_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4346_; 
v___x_4340_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2___closed__3);
v___x_4341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4339_);
lean_ctor_set(v___x_4341_, 1, v___x_4340_);
v___x_4342_ = l_Lean_MessageData_ofExpr(v_snd_4330_);
v___x_4343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4341_);
lean_ctor_set(v___x_4343_, 1, v___x_4342_);
v___x_4344_ = l_Lean_MessageData_paren(v___x_4343_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 1, v_a_4322_);
lean_ctor_set(v___x_4327_, 0, v___x_4344_);
v___x_4346_ = v___x_4327_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v___x_4344_);
lean_ctor_set(v_reuseFailAlloc_4348_, 1, v_a_4322_);
v___x_4346_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
v_a_4321_ = v_tail_4325_;
v_a_4322_ = v___x_4346_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3(lean_object* v_cls_4352_, lean_object* v_msg_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v_ref_4359_; lean_object* v___x_4360_; lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4406_; 
v_ref_4359_ = lean_ctor_get(v___y_4356_, 2);
v___x_4360_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5_spec__8(v_msg_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4363_ = v___x_4360_;
v_isShared_4364_ = v_isSharedCheck_4406_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4360_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4406_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4365_; lean_object* v_traceState_4366_; lean_object* v_env_4367_; lean_object* v_nextMacroScope_4368_; lean_object* v_ngen_4369_; lean_object* v_auxDeclNGen_4370_; lean_object* v_cache_4371_; lean_object* v_recordedDeps_4372_; lean_object* v_messages_4373_; lean_object* v_infoState_4374_; lean_object* v_snapshotTasks_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4405_; 
v___x_4365_ = lean_st_ref_take(v___y_4357_);
v_traceState_4366_ = lean_ctor_get(v___x_4365_, 4);
v_env_4367_ = lean_ctor_get(v___x_4365_, 0);
v_nextMacroScope_4368_ = lean_ctor_get(v___x_4365_, 1);
v_ngen_4369_ = lean_ctor_get(v___x_4365_, 2);
v_auxDeclNGen_4370_ = lean_ctor_get(v___x_4365_, 3);
v_cache_4371_ = lean_ctor_get(v___x_4365_, 5);
v_recordedDeps_4372_ = lean_ctor_get(v___x_4365_, 6);
v_messages_4373_ = lean_ctor_get(v___x_4365_, 7);
v_infoState_4374_ = lean_ctor_get(v___x_4365_, 8);
v_snapshotTasks_4375_ = lean_ctor_get(v___x_4365_, 9);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4377_ = v___x_4365_;
v_isShared_4378_ = v_isSharedCheck_4405_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_snapshotTasks_4375_);
lean_inc(v_infoState_4374_);
lean_inc(v_messages_4373_);
lean_inc(v_recordedDeps_4372_);
lean_inc(v_cache_4371_);
lean_inc(v_traceState_4366_);
lean_inc(v_auxDeclNGen_4370_);
lean_inc(v_ngen_4369_);
lean_inc(v_nextMacroScope_4368_);
lean_inc(v_env_4367_);
lean_dec(v___x_4365_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4405_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
uint64_t v_tid_4379_; lean_object* v_traces_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4404_; 
v_tid_4379_ = lean_ctor_get_uint64(v_traceState_4366_, sizeof(void*)*1);
v_traces_4380_ = lean_ctor_get(v_traceState_4366_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v_traceState_4366_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4382_ = v_traceState_4366_;
v_isShared_4383_ = v_isSharedCheck_4404_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_traces_4380_);
lean_dec(v_traceState_4366_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4404_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; double v___x_4386_; uint8_t v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4395_; 
v___x_4384_ = lean_box(0);
v___x_4385_ = lean_box(0);
v___x_4386_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0);
v___x_4387_ = 0;
v___x_4388_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__1));
v___x_4389_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4389_, 0, v_cls_4352_);
lean_ctor_set(v___x_4389_, 1, v___x_4385_);
lean_ctor_set(v___x_4389_, 2, v___x_4388_);
lean_ctor_set_float(v___x_4389_, sizeof(void*)*3, v___x_4386_);
lean_ctor_set_float(v___x_4389_, sizeof(void*)*3 + 8, v___x_4386_);
lean_ctor_set_uint8(v___x_4389_, sizeof(void*)*3 + 16, v___x_4387_);
v___x_4390_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__2));
v___x_4391_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4389_);
lean_ctor_set(v___x_4391_, 1, v_a_4361_);
lean_ctor_set(v___x_4391_, 2, v___x_4390_);
lean_inc(v_ref_4359_);
v___x_4392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4392_, 0, v_ref_4359_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = l_Lean_PersistentArray_push___redArg(v_traces_4380_, v___x_4392_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 0, v___x_4393_);
v___x_4395_ = v___x_4382_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4393_);
lean_ctor_set_uint64(v_reuseFailAlloc_4403_, sizeof(void*)*1, v_tid_4379_);
v___x_4395_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
lean_object* v___x_4397_; 
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 4, v___x_4395_);
v___x_4397_ = v___x_4377_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_env_4367_);
lean_ctor_set(v_reuseFailAlloc_4402_, 1, v_nextMacroScope_4368_);
lean_ctor_set(v_reuseFailAlloc_4402_, 2, v_ngen_4369_);
lean_ctor_set(v_reuseFailAlloc_4402_, 3, v_auxDeclNGen_4370_);
lean_ctor_set(v_reuseFailAlloc_4402_, 4, v___x_4395_);
lean_ctor_set(v_reuseFailAlloc_4402_, 5, v_cache_4371_);
lean_ctor_set(v_reuseFailAlloc_4402_, 6, v_recordedDeps_4372_);
lean_ctor_set(v_reuseFailAlloc_4402_, 7, v_messages_4373_);
lean_ctor_set(v_reuseFailAlloc_4402_, 8, v_infoState_4374_);
lean_ctor_set(v_reuseFailAlloc_4402_, 9, v_snapshotTasks_4375_);
v___x_4397_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
lean_object* v___x_4398_; lean_object* v___x_4400_; 
v___x_4398_ = lean_st_ref_put(v___y_4357_, v___x_4397_);
if (v_isShared_4364_ == 0)
{
lean_ctor_set(v___x_4363_, 0, v___x_4384_);
v___x_4400_ = v___x_4363_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4384_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3___boxed(lean_object* v_cls_4407_, lean_object* v_msg_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3(v_cls_4407_, v_msg_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0_spec__3(lean_object* v_msg_4415_){
_start:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4416_ = l_Lean_Meta_Tactic_BVDecide_EPR_instInhabitedSortInfo_default;
v___x_4417_ = lean_panic_fn_borrowed(v___x_4416_, v_msg_4415_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0(lean_object* v_a_4418_, lean_object* v_x_4419_){
_start:
{
if (lean_obj_tag(v_x_4419_) == 0)
{
lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4420_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__3_spec__5___closed__3);
v___x_4421_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0_spec__3(v___x_4420_);
return v___x_4421_;
}
else
{
lean_object* v_key_4422_; lean_object* v_value_4423_; lean_object* v_tail_4424_; uint8_t v___x_4425_; 
v_key_4422_ = lean_ctor_get(v_x_4419_, 0);
v_value_4423_ = lean_ctor_get(v_x_4419_, 1);
v_tail_4424_ = lean_ctor_get(v_x_4419_, 2);
v___x_4425_ = lean_nat_dec_eq(v_key_4422_, v_a_4418_);
if (v___x_4425_ == 0)
{
v_x_4419_ = v_tail_4424_;
goto _start;
}
else
{
lean_inc(v_value_4423_);
return v_value_4423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0___boxed(lean_object* v_a_4427_, lean_object* v_x_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0(v_a_4427_, v_x_4428_);
lean_dec(v_x_4428_);
lean_dec(v_a_4427_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0(lean_object* v_m_4430_, lean_object* v_a_4431_){
_start:
{
lean_object* v_buckets_4432_; lean_object* v___x_4433_; uint64_t v___x_4434_; uint64_t v___x_4435_; uint64_t v___x_4436_; uint64_t v_fold_4437_; uint64_t v___x_4438_; uint64_t v___x_4439_; uint64_t v___x_4440_; size_t v___x_4441_; size_t v___x_4442_; size_t v___x_4443_; size_t v___x_4444_; size_t v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v_buckets_4432_ = lean_ctor_get(v_m_4430_, 1);
v___x_4433_ = lean_array_get_size(v_buckets_4432_);
v___x_4434_ = l_Lean_Meta_Tactic_BVDecide_EPR_instHashableSortId_hash(v_a_4431_);
v___x_4435_ = 32ULL;
v___x_4436_ = lean_uint64_shift_right(v___x_4434_, v___x_4435_);
v_fold_4437_ = lean_uint64_xor(v___x_4434_, v___x_4436_);
v___x_4438_ = 16ULL;
v___x_4439_ = lean_uint64_shift_right(v_fold_4437_, v___x_4438_);
v___x_4440_ = lean_uint64_xor(v_fold_4437_, v___x_4439_);
v___x_4441_ = lean_uint64_to_usize(v___x_4440_);
v___x_4442_ = lean_usize_of_nat(v___x_4433_);
v___x_4443_ = ((size_t)1ULL);
v___x_4444_ = lean_usize_sub(v___x_4442_, v___x_4443_);
v___x_4445_ = lean_usize_land(v___x_4441_, v___x_4444_);
v___x_4446_ = lean_array_uget_borrowed(v_buckets_4432_, v___x_4445_);
v___x_4447_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0_spec__0(v_a_4431_, v___x_4446_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0___boxed(lean_object* v_m_4448_, lean_object* v_a_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0(v_m_4448_, v_a_4449_);
lean_dec(v_a_4449_);
lean_dec_ref(v_m_4448_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__1(lean_object* v___x_4451_, size_t v_sz_4452_, size_t v_i_4453_, lean_object* v_bs_4454_){
_start:
{
uint8_t v___x_4455_; 
v___x_4455_ = lean_usize_dec_lt(v_i_4453_, v_sz_4452_);
if (v___x_4455_ == 0)
{
return v_bs_4454_;
}
else
{
lean_object* v_v_4456_; lean_object* v___x_4457_; lean_object* v_type_4458_; lean_object* v___x_4459_; lean_object* v_bs_x27_4460_; lean_object* v___x_4461_; size_t v___x_4462_; size_t v___x_4463_; lean_object* v___x_4464_; 
v_v_4456_ = lean_array_uget(v_bs_4454_, v_i_4453_);
v___x_4457_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__0(v___x_4451_, v_v_4456_);
v_type_4458_ = lean_ctor_get(v___x_4457_, 0);
lean_inc_ref(v_type_4458_);
lean_dec_ref(v___x_4457_);
v___x_4459_ = lean_unsigned_to_nat(0u);
v_bs_x27_4460_ = lean_array_uset(v_bs_4454_, v_i_4453_, v___x_4459_);
v___x_4461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4461_, 0, v_v_4456_);
lean_ctor_set(v___x_4461_, 1, v_type_4458_);
v___x_4462_ = ((size_t)1ULL);
v___x_4463_ = lean_usize_add(v_i_4453_, v___x_4462_);
v___x_4464_ = lean_array_uset(v_bs_x27_4460_, v_i_4453_, v___x_4461_);
v_i_4453_ = v___x_4463_;
v_bs_4454_ = v___x_4464_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__1___boxed(lean_object* v___x_4466_, lean_object* v_sz_4467_, lean_object* v_i_4468_, lean_object* v_bs_4469_){
_start:
{
size_t v_sz_boxed_4470_; size_t v_i_boxed_4471_; lean_object* v_res_4472_; 
v_sz_boxed_4470_ = lean_unbox_usize(v_sz_4467_);
lean_dec(v_sz_4467_);
v_i_boxed_4471_ = lean_unbox_usize(v_i_4468_);
lean_dec(v_i_4468_);
v_res_4472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__1(v___x_4466_, v_sz_boxed_4470_, v_i_boxed_4471_, v_bs_4469_);
lean_dec_ref(v___x_4466_);
return v_res_4472_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__1(void){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__0));
v___x_4475_ = l_Lean_stringToMessageData(v___x_4474_);
return v___x_4475_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__3(void){
_start:
{
lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__2));
v___x_4478_ = l_Lean_stringToMessageData(v___x_4477_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8(lean_object* v___x_4479_, lean_object* v_as_4480_, size_t v_sz_4481_, size_t v_i_4482_, lean_object* v_b_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_){
_start:
{
lean_object* v_a_4490_; uint8_t v___x_4494_; 
v___x_4494_ = lean_usize_dec_lt(v_i_4482_, v_sz_4481_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4495_; 
v___x_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4495_, 0, v_b_4483_);
return v___x_4495_;
}
else
{
lean_object* v_a_4496_; lean_object* v_snd_4497_; lean_object* v_toCold_4498_; lean_object* v_options_4499_; lean_object* v_fst_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4527_; 
v_a_4496_ = lean_array_uget(v_as_4480_, v_i_4482_);
v_snd_4497_ = lean_ctor_get(v_a_4496_, 1);
lean_inc(v_snd_4497_);
v_toCold_4498_ = lean_ctor_get(v___y_4486_, 0);
v_options_4499_ = lean_ctor_get(v_toCold_4498_, 2);
v_fst_4500_ = lean_ctor_get(v_a_4496_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v_a_4496_);
if (v_isSharedCheck_4527_ == 0)
{
lean_object* v_unused_4528_; 
v_unused_4528_ = lean_ctor_get(v_a_4496_, 1);
lean_dec(v_unused_4528_);
v___x_4502_ = v_a_4496_;
v_isShared_4503_ = v_isSharedCheck_4527_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_fst_4500_);
lean_dec(v_a_4496_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4527_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v_argumentSorts_4504_; lean_object* v_inheritedTraceOptions_4505_; uint8_t v_hasTrace_4506_; lean_object* v___x_4507_; 
v_argumentSorts_4504_ = lean_ctor_get(v_snd_4497_, 0);
lean_inc_ref(v_argumentSorts_4504_);
lean_dec(v_snd_4497_);
v_inheritedTraceOptions_4505_ = lean_ctor_get(v_toCold_4498_, 11);
v_hasTrace_4506_ = lean_ctor_get_uint8(v_options_4499_, sizeof(void*)*1);
v___x_4507_ = lean_box(0);
if (v_hasTrace_4506_ == 0)
{
lean_dec_ref(v_argumentSorts_4504_);
lean_del_object(v___x_4502_);
lean_dec(v_fst_4500_);
v_a_4490_ = v___x_4507_;
goto v___jp_4489_;
}
else
{
lean_object* v_cls_4508_; lean_object* v___x_4509_; uint8_t v___x_4510_; 
v_cls_4508_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_4509_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9);
v___x_4510_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4505_, v_options_4499_, v___x_4509_);
if (v___x_4510_ == 0)
{
lean_dec_ref(v_argumentSorts_4504_);
lean_del_object(v___x_4502_);
lean_dec(v_fst_4500_);
v_a_4490_ = v___x_4507_;
goto v___jp_4489_;
}
else
{
size_t v_sz_4511_; size_t v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4517_; 
v_sz_4511_ = lean_array_size(v_argumentSorts_4504_);
v___x_4512_ = ((size_t)0ULL);
v___x_4513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__1(v___x_4479_, v_sz_4511_, v___x_4512_, v_argumentSorts_4504_);
v___x_4514_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__1);
v___x_4515_ = l_Lean_MessageData_ofExpr(v_fst_4500_);
if (v_isShared_4503_ == 0)
{
lean_ctor_set_tag(v___x_4502_, 7);
lean_ctor_set(v___x_4502_, 1, v___x_4515_);
lean_ctor_set(v___x_4502_, 0, v___x_4514_);
v___x_4517_ = v___x_4502_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4514_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v___x_4515_);
v___x_4517_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4518_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___closed__3);
v___x_4519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4517_);
lean_ctor_set(v___x_4519_, 1, v___x_4518_);
v___x_4520_ = lean_array_to_list(v___x_4513_);
v___x_4521_ = lean_box(0);
v___x_4522_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__2(v___x_4520_, v___x_4521_);
v___x_4523_ = l_Lean_MessageData_ofList(v___x_4522_);
v___x_4524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4519_);
lean_ctor_set(v___x_4524_, 1, v___x_4523_);
v___x_4525_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3(v_cls_4508_, v___x_4524_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_dec_ref_known(v___x_4525_, 1);
v_a_4490_ = v___x_4507_;
goto v___jp_4489_;
}
else
{
return v___x_4525_;
}
}
}
}
}
}
v___jp_4489_:
{
size_t v___x_4491_; size_t v___x_4492_; 
v___x_4491_ = ((size_t)1ULL);
v___x_4492_ = lean_usize_add(v_i_4482_, v___x_4491_);
v_i_4482_ = v___x_4492_;
v_b_4483_ = v_a_4490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8___boxed(lean_object* v___x_4529_, lean_object* v_as_4530_, lean_object* v_sz_4531_, lean_object* v_i_4532_, lean_object* v_b_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
size_t v_sz_boxed_4539_; size_t v_i_boxed_4540_; lean_object* v_res_4541_; 
v_sz_boxed_4539_ = lean_unbox_usize(v_sz_4531_);
lean_dec(v_sz_4531_);
v_i_boxed_4540_ = lean_unbox_usize(v_i_4532_);
lean_dec(v_i_4532_);
v_res_4541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8(v___x_4529_, v_as_4530_, v_sz_boxed_4539_, v_i_boxed_4540_, v_b_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec_ref(v_as_4530_);
lean_dec_ref(v___x_4529_);
return v_res_4541_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__0));
v___x_4544_ = l_Lean_stringToMessageData(v___x_4543_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9(lean_object* v_as_4545_, size_t v_sz_4546_, size_t v_i_4547_, lean_object* v_b_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v_a_4555_; uint8_t v___x_4559_; 
v___x_4559_ = lean_usize_dec_lt(v_i_4547_, v_sz_4546_);
if (v___x_4559_ == 0)
{
lean_object* v___x_4560_; 
v___x_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4560_, 0, v_b_4548_);
return v___x_4560_;
}
else
{
lean_object* v_toCold_4561_; lean_object* v_options_4562_; lean_object* v_inheritedTraceOptions_4563_; uint8_t v_hasTrace_4564_; lean_object* v___x_4565_; 
v_toCold_4561_ = lean_ctor_get(v___y_4551_, 0);
v_options_4562_ = lean_ctor_get(v_toCold_4561_, 2);
v_inheritedTraceOptions_4563_ = lean_ctor_get(v_toCold_4561_, 11);
v_hasTrace_4564_ = lean_ctor_get_uint8(v_options_4562_, sizeof(void*)*1);
v___x_4565_ = lean_box(0);
if (v_hasTrace_4564_ == 0)
{
v_a_4555_ = v___x_4565_;
goto v___jp_4554_;
}
else
{
lean_object* v_cls_4566_; lean_object* v___x_4567_; uint8_t v___x_4568_; 
v_cls_4566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_4567_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9);
v___x_4568_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4563_, v_options_4562_, v___x_4567_);
if (v___x_4568_ == 0)
{
v_a_4555_ = v___x_4565_;
goto v___jp_4554_;
}
else
{
lean_object* v_a_4569_; lean_object* v_type_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v_a_4569_ = lean_array_uget_borrowed(v_as_4545_, v_i_4547_);
v_type_4570_ = lean_ctor_get(v_a_4569_, 1);
v___x_4571_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___closed__1);
lean_inc_ref(v_type_4570_);
v___x_4572_ = l_Lean_MessageData_ofExpr(v_type_4570_);
v___x_4573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4571_);
lean_ctor_set(v___x_4573_, 1, v___x_4572_);
v___x_4574_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3(v_cls_4566_, v___x_4573_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_dec_ref_known(v___x_4574_, 1);
v_a_4555_ = v___x_4565_;
goto v___jp_4554_;
}
else
{
return v___x_4574_;
}
}
}
}
v___jp_4554_:
{
size_t v___x_4556_; size_t v___x_4557_; 
v___x_4556_ = ((size_t)1ULL);
v___x_4557_ = lean_usize_add(v_i_4547_, v___x_4556_);
v_i_4547_ = v___x_4557_;
v_b_4548_ = v_a_4555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9___boxed(lean_object* v_as_4575_, lean_object* v_sz_4576_, lean_object* v_i_4577_, lean_object* v_b_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
size_t v_sz_boxed_4584_; size_t v_i_boxed_4585_; lean_object* v_res_4586_; 
v_sz_boxed_4584_ = lean_unbox_usize(v_sz_4576_);
lean_dec(v_sz_4576_);
v_i_boxed_4585_ = lean_unbox_usize(v_i_4577_);
lean_dec(v_i_4577_);
v_res_4586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9(v_as_4575_, v_sz_boxed_4584_, v_i_boxed_4585_, v_b_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec_ref(v_as_4575_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__12(lean_object* v_x_4587_, lean_object* v_x_4588_){
_start:
{
if (lean_obj_tag(v_x_4588_) == 0)
{
return v_x_4587_;
}
else
{
lean_object* v_key_4589_; lean_object* v_value_4590_; lean_object* v_tail_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v_key_4589_ = lean_ctor_get(v_x_4588_, 0);
v_value_4590_ = lean_ctor_get(v_x_4588_, 1);
v_tail_4591_ = lean_ctor_get(v_x_4588_, 2);
lean_inc(v_value_4590_);
lean_inc(v_key_4589_);
v___x_4592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4592_, 0, v_key_4589_);
lean_ctor_set(v___x_4592_, 1, v_value_4590_);
v___x_4593_ = lean_array_push(v_x_4587_, v___x_4592_);
v_x_4587_ = v___x_4593_;
v_x_4588_ = v_tail_4591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__12___boxed(lean_object* v_x_4595_, lean_object* v_x_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__12(v_x_4595_, v_x_4596_);
lean_dec(v_x_4596_);
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13(lean_object* v_as_4598_, size_t v_i_4599_, size_t v_stop_4600_, lean_object* v_b_4601_){
_start:
{
uint8_t v___x_4602_; 
v___x_4602_ = lean_usize_dec_eq(v_i_4599_, v_stop_4600_);
if (v___x_4602_ == 0)
{
lean_object* v___x_4603_; lean_object* v___x_4604_; size_t v___x_4605_; size_t v___x_4606_; 
v___x_4603_ = lean_array_uget_borrowed(v_as_4598_, v_i_4599_);
v___x_4604_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__12(v_b_4601_, v___x_4603_);
v___x_4605_ = ((size_t)1ULL);
v___x_4606_ = lean_usize_add(v_i_4599_, v___x_4605_);
v_i_4599_ = v___x_4606_;
v_b_4601_ = v___x_4604_;
goto _start;
}
else
{
return v_b_4601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13___boxed(lean_object* v_as_4608_, lean_object* v_i_4609_, lean_object* v_stop_4610_, lean_object* v_b_4611_){
_start:
{
size_t v_i_boxed_4612_; size_t v_stop_boxed_4613_; lean_object* v_res_4614_; 
v_i_boxed_4612_ = lean_unbox_usize(v_i_4609_);
lean_dec(v_i_4609_);
v_stop_boxed_4613_ = lean_unbox_usize(v_stop_4610_);
lean_dec(v_stop_4610_);
v_res_4614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13(v_as_4608_, v_i_boxed_4612_, v_stop_boxed_4613_, v_b_4611_);
lean_dec_ref(v_as_4608_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___redArg(lean_object* v_hi_4615_, lean_object* v_pivot_4616_, lean_object* v_as_4617_, lean_object* v_i_4618_, lean_object* v_k_4619_){
_start:
{
uint8_t v___x_4620_; 
v___x_4620_ = lean_nat_dec_lt(v_k_4619_, v_hi_4615_);
if (v___x_4620_ == 0)
{
lean_object* v___x_4621_; lean_object* v___x_4622_; 
lean_dec(v_k_4619_);
v___x_4621_ = lean_array_fswap(v_as_4617_, v_i_4618_, v_hi_4615_);
v___x_4622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4622_, 0, v_i_4618_);
lean_ctor_set(v___x_4622_, 1, v___x_4621_);
return v___x_4622_;
}
else
{
lean_object* v___x_4623_; lean_object* v_fst_4624_; lean_object* v_fst_4625_; uint8_t v___x_4626_; 
v___x_4623_ = lean_array_fget_borrowed(v_as_4617_, v_k_4619_);
v_fst_4624_ = lean_ctor_get(v___x_4623_, 0);
v_fst_4625_ = lean_ctor_get(v_pivot_4616_, 0);
v___x_4626_ = lean_expr_lt(v_fst_4624_, v_fst_4625_);
if (v___x_4626_ == 0)
{
lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4627_ = lean_unsigned_to_nat(1u);
v___x_4628_ = lean_nat_add(v_k_4619_, v___x_4627_);
lean_dec(v_k_4619_);
v_k_4619_ = v___x_4628_;
goto _start;
}
else
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4630_ = lean_array_fswap(v_as_4617_, v_i_4618_, v_k_4619_);
v___x_4631_ = lean_unsigned_to_nat(1u);
v___x_4632_ = lean_nat_add(v_i_4618_, v___x_4631_);
lean_dec(v_i_4618_);
v___x_4633_ = lean_nat_add(v_k_4619_, v___x_4631_);
lean_dec(v_k_4619_);
v_as_4617_ = v___x_4630_;
v_i_4618_ = v___x_4632_;
v_k_4619_ = v___x_4633_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___redArg___boxed(lean_object* v_hi_4635_, lean_object* v_pivot_4636_, lean_object* v_as_4637_, lean_object* v_i_4638_, lean_object* v_k_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___redArg(v_hi_4635_, v_pivot_4636_, v_as_4637_, v_i_4638_, v_k_4639_);
lean_dec_ref(v_pivot_4636_);
lean_dec(v_hi_4635_);
return v_res_4640_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0(lean_object* v_x1_4641_, lean_object* v_x2_4642_){
_start:
{
lean_object* v_fst_4643_; lean_object* v_fst_4644_; uint8_t v___x_4645_; 
v_fst_4643_ = lean_ctor_get(v_x1_4641_, 0);
v_fst_4644_ = lean_ctor_get(v_x2_4642_, 0);
v___x_4645_ = lean_expr_lt(v_fst_4643_, v_fst_4644_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0___boxed(lean_object* v_x1_4646_, lean_object* v_x2_4647_){
_start:
{
uint8_t v_res_4648_; lean_object* v_r_4649_; 
v_res_4648_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0(v_x1_4646_, v_x2_4647_);
lean_dec_ref(v_x2_4647_);
lean_dec_ref(v_x1_4646_);
v_r_4649_ = lean_box(v_res_4648_);
return v_r_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(lean_object* v_n_4650_, lean_object* v_as_4651_, lean_object* v_lo_4652_, lean_object* v_hi_4653_){
_start:
{
lean_object* v___y_4655_; uint8_t v___x_4665_; 
v___x_4665_ = lean_nat_dec_lt(v_lo_4652_, v_hi_4653_);
if (v___x_4665_ == 0)
{
lean_dec(v_lo_4652_);
return v_as_4651_;
}
else
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v_mid_4668_; lean_object* v___y_4670_; lean_object* v___y_4676_; lean_object* v___x_4681_; lean_object* v___x_4682_; uint8_t v___x_4683_; 
v___x_4666_ = lean_nat_add(v_lo_4652_, v_hi_4653_);
v___x_4667_ = lean_unsigned_to_nat(1u);
v_mid_4668_ = lean_nat_shiftr(v___x_4666_, v___x_4667_);
lean_dec(v___x_4666_);
v___x_4681_ = lean_array_fget_borrowed(v_as_4651_, v_mid_4668_);
v___x_4682_ = lean_array_fget_borrowed(v_as_4651_, v_lo_4652_);
v___x_4683_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0(v___x_4681_, v___x_4682_);
if (v___x_4683_ == 0)
{
v___y_4676_ = v_as_4651_;
goto v___jp_4675_;
}
else
{
lean_object* v___x_4684_; 
v___x_4684_ = lean_array_fswap(v_as_4651_, v_lo_4652_, v_mid_4668_);
v___y_4676_ = v___x_4684_;
goto v___jp_4675_;
}
v___jp_4669_:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; uint8_t v___x_4673_; 
v___x_4671_ = lean_array_fget_borrowed(v___y_4670_, v_mid_4668_);
v___x_4672_ = lean_array_fget_borrowed(v___y_4670_, v_hi_4653_);
v___x_4673_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0(v___x_4671_, v___x_4672_);
if (v___x_4673_ == 0)
{
lean_dec(v_mid_4668_);
v___y_4655_ = v___y_4670_;
goto v___jp_4654_;
}
else
{
lean_object* v___x_4674_; 
v___x_4674_ = lean_array_fswap(v___y_4670_, v_mid_4668_, v_hi_4653_);
lean_dec(v_mid_4668_);
v___y_4655_ = v___x_4674_;
goto v___jp_4654_;
}
}
v___jp_4675_:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; uint8_t v___x_4679_; 
v___x_4677_ = lean_array_fget_borrowed(v___y_4676_, v_hi_4653_);
v___x_4678_ = lean_array_fget_borrowed(v___y_4676_, v_lo_4652_);
v___x_4679_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___lam__0(v___x_4677_, v___x_4678_);
if (v___x_4679_ == 0)
{
v___y_4670_ = v___y_4676_;
goto v___jp_4669_;
}
else
{
lean_object* v___x_4680_; 
v___x_4680_ = lean_array_fswap(v___y_4676_, v_lo_4652_, v_hi_4653_);
v___y_4670_ = v___x_4680_;
goto v___jp_4669_;
}
}
}
v___jp_4654_:
{
lean_object* v_pivot_4656_; lean_object* v___x_4657_; lean_object* v_fst_4658_; lean_object* v_snd_4659_; uint8_t v___x_4660_; 
v_pivot_4656_ = lean_array_fget(v___y_4655_, v_hi_4653_);
lean_inc_n(v_lo_4652_, 2);
v___x_4657_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___redArg(v_hi_4653_, v_pivot_4656_, v___y_4655_, v_lo_4652_, v_lo_4652_);
lean_dec(v_pivot_4656_);
v_fst_4658_ = lean_ctor_get(v___x_4657_, 0);
lean_inc(v_fst_4658_);
v_snd_4659_ = lean_ctor_get(v___x_4657_, 1);
lean_inc(v_snd_4659_);
lean_dec_ref(v___x_4657_);
v___x_4660_ = lean_nat_dec_le(v_hi_4653_, v_fst_4658_);
if (v___x_4660_ == 0)
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4661_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v_n_4650_, v_snd_4659_, v_lo_4652_, v_fst_4658_);
v___x_4662_ = lean_unsigned_to_nat(1u);
v___x_4663_ = lean_nat_add(v_fst_4658_, v___x_4662_);
lean_dec(v_fst_4658_);
v_as_4651_ = v___x_4661_;
v_lo_4652_ = v___x_4663_;
goto _start;
}
else
{
lean_dec(v_fst_4658_);
lean_dec(v_lo_4652_);
return v_snd_4659_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg___boxed(lean_object* v_n_4685_, lean_object* v_as_4686_, lean_object* v_lo_4687_, lean_object* v_hi_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v_n_4685_, v_as_4686_, v_lo_4687_, v_hi_4688_);
lean_dec(v_hi_4688_);
lean_dec(v_n_4685_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___redArg(lean_object* v_hi_4690_, lean_object* v_pivot_4691_, lean_object* v_as_4692_, lean_object* v_i_4693_, lean_object* v_k_4694_){
_start:
{
uint8_t v___x_4695_; 
v___x_4695_ = lean_nat_dec_lt(v_k_4694_, v_hi_4690_);
if (v___x_4695_ == 0)
{
lean_object* v___x_4696_; lean_object* v___x_4697_; 
lean_dec(v_k_4694_);
v___x_4696_ = lean_array_fswap(v_as_4692_, v_i_4693_, v_hi_4690_);
v___x_4697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4697_, 0, v_i_4693_);
lean_ctor_set(v___x_4697_, 1, v___x_4696_);
return v___x_4697_;
}
else
{
lean_object* v___x_4698_; lean_object* v_fst_4699_; lean_object* v_fst_4700_; uint8_t v___x_4701_; 
v___x_4698_ = lean_array_fget_borrowed(v_as_4692_, v_k_4694_);
v_fst_4699_ = lean_ctor_get(v___x_4698_, 0);
v_fst_4700_ = lean_ctor_get(v_pivot_4691_, 0);
v___x_4701_ = lean_nat_dec_lt(v_fst_4699_, v_fst_4700_);
if (v___x_4701_ == 0)
{
lean_object* v___x_4702_; lean_object* v___x_4703_; 
v___x_4702_ = lean_unsigned_to_nat(1u);
v___x_4703_ = lean_nat_add(v_k_4694_, v___x_4702_);
lean_dec(v_k_4694_);
v_k_4694_ = v___x_4703_;
goto _start;
}
else
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4705_ = lean_array_fswap(v_as_4692_, v_i_4693_, v_k_4694_);
v___x_4706_ = lean_unsigned_to_nat(1u);
v___x_4707_ = lean_nat_add(v_i_4693_, v___x_4706_);
lean_dec(v_i_4693_);
v___x_4708_ = lean_nat_add(v_k_4694_, v___x_4706_);
lean_dec(v_k_4694_);
v_as_4692_ = v___x_4705_;
v_i_4693_ = v___x_4707_;
v_k_4694_ = v___x_4708_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___redArg___boxed(lean_object* v_hi_4710_, lean_object* v_pivot_4711_, lean_object* v_as_4712_, lean_object* v_i_4713_, lean_object* v_k_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___redArg(v_hi_4710_, v_pivot_4711_, v_as_4712_, v_i_4713_, v_k_4714_);
lean_dec_ref(v_pivot_4711_);
lean_dec(v_hi_4710_);
return v_res_4715_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0(lean_object* v_x1_4716_, lean_object* v_x2_4717_){
_start:
{
lean_object* v_fst_4718_; lean_object* v_fst_4719_; uint8_t v___x_4720_; 
v_fst_4718_ = lean_ctor_get(v_x1_4716_, 0);
v_fst_4719_ = lean_ctor_get(v_x2_4717_, 0);
v___x_4720_ = lean_nat_dec_lt(v_fst_4718_, v_fst_4719_);
return v___x_4720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0___boxed(lean_object* v_x1_4721_, lean_object* v_x2_4722_){
_start:
{
uint8_t v_res_4723_; lean_object* v_r_4724_; 
v_res_4723_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0(v_x1_4721_, v_x2_4722_);
lean_dec_ref(v_x2_4722_);
lean_dec_ref(v_x1_4721_);
v_r_4724_ = lean_box(v_res_4723_);
return v_r_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg(lean_object* v_n_4725_, lean_object* v_as_4726_, lean_object* v_lo_4727_, lean_object* v_hi_4728_){
_start:
{
lean_object* v___y_4730_; uint8_t v___x_4740_; 
v___x_4740_ = lean_nat_dec_lt(v_lo_4727_, v_hi_4728_);
if (v___x_4740_ == 0)
{
lean_dec(v_lo_4727_);
return v_as_4726_;
}
else
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v_mid_4743_; lean_object* v___y_4745_; lean_object* v___y_4751_; lean_object* v___x_4756_; lean_object* v___x_4757_; uint8_t v___x_4758_; 
v___x_4741_ = lean_nat_add(v_lo_4727_, v_hi_4728_);
v___x_4742_ = lean_unsigned_to_nat(1u);
v_mid_4743_ = lean_nat_shiftr(v___x_4741_, v___x_4742_);
lean_dec(v___x_4741_);
v___x_4756_ = lean_array_fget_borrowed(v_as_4726_, v_mid_4743_);
v___x_4757_ = lean_array_fget_borrowed(v_as_4726_, v_lo_4727_);
v___x_4758_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0(v___x_4756_, v___x_4757_);
if (v___x_4758_ == 0)
{
v___y_4751_ = v_as_4726_;
goto v___jp_4750_;
}
else
{
lean_object* v___x_4759_; 
v___x_4759_ = lean_array_fswap(v_as_4726_, v_lo_4727_, v_mid_4743_);
v___y_4751_ = v___x_4759_;
goto v___jp_4750_;
}
v___jp_4744_:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; 
v___x_4746_ = lean_array_fget_borrowed(v___y_4745_, v_mid_4743_);
v___x_4747_ = lean_array_fget_borrowed(v___y_4745_, v_hi_4728_);
v___x_4748_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0(v___x_4746_, v___x_4747_);
if (v___x_4748_ == 0)
{
lean_dec(v_mid_4743_);
v___y_4730_ = v___y_4745_;
goto v___jp_4729_;
}
else
{
lean_object* v___x_4749_; 
v___x_4749_ = lean_array_fswap(v___y_4745_, v_mid_4743_, v_hi_4728_);
lean_dec(v_mid_4743_);
v___y_4730_ = v___x_4749_;
goto v___jp_4729_;
}
}
v___jp_4750_:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; uint8_t v___x_4754_; 
v___x_4752_ = lean_array_fget_borrowed(v___y_4751_, v_hi_4728_);
v___x_4753_ = lean_array_fget_borrowed(v___y_4751_, v_lo_4727_);
v___x_4754_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___lam__0(v___x_4752_, v___x_4753_);
if (v___x_4754_ == 0)
{
v___y_4745_ = v___y_4751_;
goto v___jp_4744_;
}
else
{
lean_object* v___x_4755_; 
v___x_4755_ = lean_array_fswap(v___y_4751_, v_lo_4727_, v_hi_4728_);
v___y_4745_ = v___x_4755_;
goto v___jp_4744_;
}
}
}
v___jp_4729_:
{
lean_object* v_pivot_4731_; lean_object* v___x_4732_; lean_object* v_fst_4733_; lean_object* v_snd_4734_; uint8_t v___x_4735_; 
v_pivot_4731_ = lean_array_fget(v___y_4730_, v_hi_4728_);
lean_inc_n(v_lo_4727_, 2);
v___x_4732_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___redArg(v_hi_4728_, v_pivot_4731_, v___y_4730_, v_lo_4727_, v_lo_4727_);
lean_dec(v_pivot_4731_);
v_fst_4733_ = lean_ctor_get(v___x_4732_, 0);
lean_inc(v_fst_4733_);
v_snd_4734_ = lean_ctor_get(v___x_4732_, 1);
lean_inc(v_snd_4734_);
lean_dec_ref(v___x_4732_);
v___x_4735_ = lean_nat_dec_le(v_hi_4728_, v_fst_4733_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4736_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg(v_n_4725_, v_snd_4734_, v_lo_4727_, v_fst_4733_);
v___x_4737_ = lean_unsigned_to_nat(1u);
v___x_4738_ = lean_nat_add(v_fst_4733_, v___x_4737_);
lean_dec(v_fst_4733_);
v_as_4726_ = v___x_4736_;
v_lo_4727_ = v___x_4738_;
goto _start;
}
else
{
lean_dec(v_fst_4733_);
lean_dec(v_lo_4727_);
return v_snd_4734_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg___boxed(lean_object* v_n_4760_, lean_object* v_as_4761_, lean_object* v_lo_4762_, lean_object* v_hi_4763_){
_start:
{
lean_object* v_res_4764_; 
v_res_4764_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg(v_n_4760_, v_as_4761_, v_lo_4762_, v_hi_4763_);
lean_dec(v_hi_4763_);
lean_dec(v_n_4760_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__4(size_t v_sz_4765_, size_t v_i_4766_, lean_object* v_bs_4767_){
_start:
{
uint8_t v___x_4768_; 
v___x_4768_ = lean_usize_dec_lt(v_i_4766_, v_sz_4765_);
if (v___x_4768_ == 0)
{
return v_bs_4767_;
}
else
{
lean_object* v_v_4769_; lean_object* v___x_4770_; lean_object* v_bs_x27_4771_; size_t v___x_4772_; size_t v___x_4773_; lean_object* v___x_4774_; 
v_v_4769_ = lean_array_uget(v_bs_4767_, v_i_4766_);
v___x_4770_ = lean_unsigned_to_nat(0u);
v_bs_x27_4771_ = lean_array_uset(v_bs_4767_, v_i_4766_, v___x_4770_);
v___x_4772_ = ((size_t)1ULL);
v___x_4773_ = lean_usize_add(v_i_4766_, v___x_4772_);
v___x_4774_ = lean_array_uset(v_bs_x27_4771_, v_i_4766_, v_v_4769_);
v_i_4766_ = v___x_4773_;
v_bs_4767_ = v___x_4774_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__4___boxed(lean_object* v_sz_4776_, lean_object* v_i_4777_, lean_object* v_bs_4778_){
_start:
{
size_t v_sz_boxed_4779_; size_t v_i_boxed_4780_; lean_object* v_res_4781_; 
v_sz_boxed_4779_ = lean_unbox_usize(v_sz_4776_);
lean_dec(v_sz_4776_);
v_i_boxed_4780_ = lean_unbox_usize(v_i_4777_);
lean_dec(v_i_4777_);
v_res_4781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__4(v_sz_boxed_4779_, v_i_boxed_4780_, v_bs_4778_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__5(lean_object* v_a_4782_, lean_object* v_a_4783_){
_start:
{
if (lean_obj_tag(v_a_4782_) == 0)
{
lean_object* v___x_4784_; 
v___x_4784_ = l_List_reverse___redArg(v_a_4783_);
return v___x_4784_;
}
else
{
lean_object* v_head_4785_; lean_object* v_tail_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4797_; 
v_head_4785_ = lean_ctor_get(v_a_4782_, 0);
v_tail_4786_ = lean_ctor_get(v_a_4782_, 1);
v_isSharedCheck_4797_ = !lean_is_exclusive(v_a_4782_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4788_ = v_a_4782_;
v_isShared_4789_ = v_isSharedCheck_4797_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_tail_4786_);
lean_inc(v_head_4785_);
lean_dec(v_a_4782_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4797_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4794_; 
v___x_4790_ = l_Nat_reprFast(v_head_4785_);
v___x_4791_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4790_);
v___x_4792_ = l_Lean_MessageData_ofFormat(v___x_4791_);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 1, v_a_4783_);
lean_ctor_set(v___x_4788_, 0, v___x_4792_);
v___x_4794_ = v___x_4788_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v___x_4792_);
lean_ctor_set(v_reuseFailAlloc_4796_, 1, v_a_4783_);
v___x_4794_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
v_a_4782_ = v_tail_4786_;
v_a_4783_ = v___x_4794_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__1(void){
_start:
{
lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__0));
v___x_4800_ = l_Lean_stringToMessageData(v___x_4799_);
return v___x_4800_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3(void){
_start:
{
lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__2));
v___x_4803_ = l_Lean_stringToMessageData(v___x_4802_);
return v___x_4803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10(lean_object* v_as_4804_, size_t v_sz_4805_, size_t v_i_4806_, lean_object* v_b_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v_a_4814_; uint8_t v___x_4818_; 
v___x_4818_ = lean_usize_dec_lt(v_i_4806_, v_sz_4805_);
if (v___x_4818_ == 0)
{
lean_object* v___x_4819_; 
v___x_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4819_, 0, v_b_4807_);
return v___x_4819_;
}
else
{
lean_object* v_toCold_4820_; lean_object* v_options_4821_; lean_object* v_inheritedTraceOptions_4822_; uint8_t v_hasTrace_4823_; lean_object* v___x_4824_; 
v_toCold_4820_ = lean_ctor_get(v___y_4810_, 0);
v_options_4821_ = lean_ctor_get(v_toCold_4820_, 2);
v_inheritedTraceOptions_4822_ = lean_ctor_get(v_toCold_4820_, 11);
v_hasTrace_4823_ = lean_ctor_get_uint8(v_options_4821_, sizeof(void*)*1);
v___x_4824_ = lean_box(0);
if (v_hasTrace_4823_ == 0)
{
v_a_4814_ = v___x_4824_;
goto v___jp_4813_;
}
else
{
lean_object* v_cls_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; 
v_cls_4825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_4826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9);
v___x_4827_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4822_, v_options_4821_, v___x_4826_);
if (v___x_4827_ == 0)
{
v_a_4814_ = v___x_4824_;
goto v___jp_4813_;
}
else
{
lean_object* v_a_4828_; lean_object* v_hyp_4829_; lean_object* v_boundSorts_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4851_; 
v_a_4828_ = lean_array_uget(v_as_4804_, v_i_4806_);
v_hyp_4829_ = lean_ctor_get(v_a_4828_, 0);
v_boundSorts_4830_ = lean_ctor_get(v_a_4828_, 1);
v_isSharedCheck_4851_ = !lean_is_exclusive(v_a_4828_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4832_ = v_a_4828_;
v_isShared_4833_ = v_isSharedCheck_4851_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_boundSorts_4830_);
lean_inc(v_hyp_4829_);
lean_dec(v_a_4828_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4851_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v_type_4834_; size_t v_sz_4835_; lean_object* v___x_4836_; size_t v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4844_; 
v_type_4834_ = lean_ctor_get(v_hyp_4829_, 1);
lean_inc_ref(v_type_4834_);
lean_dec_ref(v_hyp_4829_);
v_sz_4835_ = lean_array_size(v_boundSorts_4830_);
v___x_4836_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__1);
v___x_4837_ = ((size_t)0ULL);
v___x_4838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__4(v_sz_4835_, v___x_4837_, v_boundSorts_4830_);
v___x_4839_ = lean_array_to_list(v___x_4838_);
v___x_4840_ = lean_box(0);
v___x_4841_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__5(v___x_4839_, v___x_4840_);
v___x_4842_ = l_Lean_MessageData_ofList(v___x_4841_);
if (v_isShared_4833_ == 0)
{
lean_ctor_set_tag(v___x_4832_, 7);
lean_ctor_set(v___x_4832_, 1, v___x_4842_);
lean_ctor_set(v___x_4832_, 0, v___x_4836_);
v___x_4844_ = v___x_4832_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4836_);
lean_ctor_set(v_reuseFailAlloc_4850_, 1, v___x_4842_);
v___x_4844_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4845_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3);
v___x_4846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4844_);
lean_ctor_set(v___x_4846_, 1, v___x_4845_);
v___x_4847_ = l_Lean_MessageData_ofExpr(v_type_4834_);
v___x_4848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4846_);
lean_ctor_set(v___x_4848_, 1, v___x_4847_);
v___x_4849_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3(v_cls_4825_, v___x_4848_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_dec_ref_known(v___x_4849_, 1);
v_a_4814_ = v___x_4824_;
goto v___jp_4813_;
}
else
{
return v___x_4849_;
}
}
}
}
}
}
v___jp_4813_:
{
size_t v___x_4815_; size_t v___x_4816_; 
v___x_4815_ = ((size_t)1ULL);
v___x_4816_ = lean_usize_add(v_i_4806_, v___x_4815_);
v_i_4806_ = v___x_4816_;
v_b_4807_ = v_a_4814_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___boxed(lean_object* v_as_4852_, lean_object* v_sz_4853_, lean_object* v_i_4854_, lean_object* v_b_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
size_t v_sz_boxed_4861_; size_t v_i_boxed_4862_; lean_object* v_res_4863_; 
v_sz_boxed_4861_ = lean_unbox_usize(v_sz_4853_);
lean_dec(v_sz_4853_);
v_i_boxed_4862_ = lean_unbox_usize(v_i_4854_);
lean_dec(v_i_4854_);
v_res_4863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10(v_as_4852_, v_sz_boxed_4861_, v_i_boxed_4862_, v_b_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec_ref(v_as_4852_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__6(lean_object* v_a_4864_, lean_object* v_a_4865_){
_start:
{
if (lean_obj_tag(v_a_4864_) == 0)
{
lean_object* v___x_4866_; 
v___x_4866_ = l_List_reverse___redArg(v_a_4865_);
return v___x_4866_;
}
else
{
lean_object* v_head_4867_; lean_object* v_tail_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4877_; 
v_head_4867_ = lean_ctor_get(v_a_4864_, 0);
v_tail_4868_ = lean_ctor_get(v_a_4864_, 1);
v_isSharedCheck_4877_ = !lean_is_exclusive(v_a_4864_);
if (v_isSharedCheck_4877_ == 0)
{
v___x_4870_ = v_a_4864_;
v_isShared_4871_ = v_isSharedCheck_4877_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_tail_4868_);
lean_inc(v_head_4867_);
lean_dec(v_a_4864_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4877_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4872_; lean_object* v___x_4874_; 
v___x_4872_ = l_Lean_MessageData_ofExpr(v_head_4867_);
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 1, v_a_4865_);
lean_ctor_set(v___x_4870_, 0, v___x_4872_);
v___x_4874_ = v___x_4870_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v___x_4872_);
lean_ctor_set(v_reuseFailAlloc_4876_, 1, v_a_4865_);
v___x_4874_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
v_a_4864_ = v_tail_4868_;
v_a_4865_ = v___x_4874_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__1(void){
_start:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__0));
v___x_4880_ = l_Lean_stringToMessageData(v___x_4879_);
return v___x_4880_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__3(void){
_start:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__2));
v___x_4883_ = l_Lean_stringToMessageData(v___x_4882_);
return v___x_4883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7(lean_object* v_as_4884_, size_t v_sz_4885_, size_t v_i_4886_, lean_object* v_b_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_){
_start:
{
lean_object* v_a_4894_; uint8_t v___x_4898_; 
v___x_4898_ = lean_usize_dec_lt(v_i_4886_, v_sz_4885_);
if (v___x_4898_ == 0)
{
lean_object* v___x_4899_; 
v___x_4899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4899_, 0, v_b_4887_);
return v___x_4899_;
}
else
{
lean_object* v_a_4900_; lean_object* v_toCold_4901_; lean_object* v_options_4902_; lean_object* v_fst_4903_; lean_object* v_snd_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4935_; 
v_a_4900_ = lean_array_uget(v_as_4884_, v_i_4886_);
v_toCold_4901_ = lean_ctor_get(v___y_4890_, 0);
v_options_4902_ = lean_ctor_get(v_toCold_4901_, 2);
v_fst_4903_ = lean_ctor_get(v_a_4900_, 0);
v_snd_4904_ = lean_ctor_get(v_a_4900_, 1);
v_isSharedCheck_4935_ = !lean_is_exclusive(v_a_4900_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4906_ = v_a_4900_;
v_isShared_4907_ = v_isSharedCheck_4935_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_snd_4904_);
lean_inc(v_fst_4903_);
lean_dec(v_a_4900_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4935_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
lean_object* v_inheritedTraceOptions_4908_; uint8_t v_hasTrace_4909_; lean_object* v___x_4910_; 
v_inheritedTraceOptions_4908_ = lean_ctor_get(v_toCold_4901_, 11);
v_hasTrace_4909_ = lean_ctor_get_uint8(v_options_4902_, sizeof(void*)*1);
v___x_4910_ = lean_box(0);
if (v_hasTrace_4909_ == 0)
{
lean_del_object(v___x_4906_);
lean_dec(v_snd_4904_);
lean_dec(v_fst_4903_);
v_a_4894_ = v___x_4910_;
goto v___jp_4893_;
}
else
{
lean_object* v_cls_4911_; lean_object* v___x_4912_; uint8_t v___x_4913_; 
v_cls_4911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_4912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9);
v___x_4913_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4908_, v_options_4902_, v___x_4912_);
if (v___x_4913_ == 0)
{
lean_del_object(v___x_4906_);
lean_dec(v_snd_4904_);
lean_dec(v_fst_4903_);
v_a_4894_ = v___x_4910_;
goto v___jp_4893_;
}
else
{
lean_object* v_type_4914_; lean_object* v_elements_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4921_; 
v_type_4914_ = lean_ctor_get(v_snd_4904_, 0);
lean_inc_ref(v_type_4914_);
v_elements_4915_ = lean_ctor_get(v_snd_4904_, 2);
lean_inc_ref(v_elements_4915_);
lean_dec(v_snd_4904_);
v___x_4916_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__1);
v___x_4917_ = l_Nat_reprFast(v_fst_4903_);
v___x_4918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4917_);
v___x_4919_ = l_Lean_MessageData_ofFormat(v___x_4918_);
if (v_isShared_4907_ == 0)
{
lean_ctor_set_tag(v___x_4906_, 7);
lean_ctor_set(v___x_4906_, 1, v___x_4919_);
lean_ctor_set(v___x_4906_, 0, v___x_4916_);
v___x_4921_ = v___x_4906_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4916_);
lean_ctor_set(v_reuseFailAlloc_4934_, 1, v___x_4919_);
v___x_4921_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4922_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10___closed__3);
v___x_4923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4923_, 0, v___x_4921_);
lean_ctor_set(v___x_4923_, 1, v___x_4922_);
v___x_4924_ = l_Lean_MessageData_ofExpr(v_type_4914_);
v___x_4925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4923_);
lean_ctor_set(v___x_4925_, 1, v___x_4924_);
v___x_4926_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___closed__3);
v___x_4927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4925_);
lean_ctor_set(v___x_4927_, 1, v___x_4926_);
v___x_4928_ = lean_array_to_list(v_elements_4915_);
v___x_4929_ = lean_box(0);
v___x_4930_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__6(v___x_4928_, v___x_4929_);
v___x_4931_ = l_Lean_MessageData_ofList(v___x_4930_);
v___x_4932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4932_, 0, v___x_4927_);
lean_ctor_set(v___x_4932_, 1, v___x_4931_);
v___x_4933_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__3(v_cls_4911_, v___x_4932_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_);
if (lean_obj_tag(v___x_4933_) == 0)
{
lean_dec_ref_known(v___x_4933_, 1);
v_a_4894_ = v___x_4910_;
goto v___jp_4893_;
}
else
{
return v___x_4933_;
}
}
}
}
}
}
v___jp_4893_:
{
size_t v___x_4895_; size_t v___x_4896_; 
v___x_4895_ = ((size_t)1ULL);
v___x_4896_ = lean_usize_add(v_i_4886_, v___x_4895_);
v_i_4886_ = v___x_4896_;
v_b_4887_ = v_a_4894_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7___boxed(lean_object* v_as_4936_, lean_object* v_sz_4937_, lean_object* v_i_4938_, lean_object* v_b_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
size_t v_sz_boxed_4945_; size_t v_i_boxed_4946_; lean_object* v_res_4947_; 
v_sz_boxed_4945_ = lean_unbox_usize(v_sz_4937_);
lean_dec(v_sz_4937_);
v_i_boxed_4946_ = lean_unbox_usize(v_i_4938_);
lean_dec(v_i_4938_);
v_res_4947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7(v_as_4936_, v_sz_boxed_4945_, v_i_boxed_4946_, v_b_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
lean_dec(v___y_4943_);
lean_dec_ref(v___y_4942_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
lean_dec_ref(v_as_4936_);
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__18(lean_object* v_x_4948_, lean_object* v_x_4949_){
_start:
{
if (lean_obj_tag(v_x_4949_) == 0)
{
return v_x_4948_;
}
else
{
lean_object* v_key_4950_; lean_object* v_value_4951_; lean_object* v_tail_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
v_key_4950_ = lean_ctor_get(v_x_4949_, 0);
v_value_4951_ = lean_ctor_get(v_x_4949_, 1);
v_tail_4952_ = lean_ctor_get(v_x_4949_, 2);
lean_inc(v_value_4951_);
lean_inc(v_key_4950_);
v___x_4953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4953_, 0, v_key_4950_);
lean_ctor_set(v___x_4953_, 1, v_value_4951_);
v___x_4954_ = lean_array_push(v_x_4948_, v___x_4953_);
v_x_4948_ = v___x_4954_;
v_x_4949_ = v_tail_4952_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__18___boxed(lean_object* v_x_4956_, lean_object* v_x_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__18(v_x_4956_, v_x_4957_);
lean_dec(v_x_4957_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__19(lean_object* v_as_4959_, size_t v_i_4960_, size_t v_stop_4961_, lean_object* v_b_4962_){
_start:
{
uint8_t v___x_4963_; 
v___x_4963_ = lean_usize_dec_eq(v_i_4960_, v_stop_4961_);
if (v___x_4963_ == 0)
{
lean_object* v___x_4964_; lean_object* v___x_4965_; size_t v___x_4966_; size_t v___x_4967_; 
v___x_4964_ = lean_array_uget_borrowed(v_as_4959_, v_i_4960_);
v___x_4965_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__18(v_b_4962_, v___x_4964_);
v___x_4966_ = ((size_t)1ULL);
v___x_4967_ = lean_usize_add(v_i_4960_, v___x_4966_);
v_i_4960_ = v___x_4967_;
v_b_4962_ = v___x_4965_;
goto _start;
}
else
{
return v_b_4962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__19___boxed(lean_object* v_as_4969_, lean_object* v_i_4970_, lean_object* v_stop_4971_, lean_object* v_b_4972_){
_start:
{
size_t v_i_boxed_4973_; size_t v_stop_boxed_4974_; lean_object* v_res_4975_; 
v_i_boxed_4973_ = lean_unbox_usize(v_i_4970_);
lean_dec(v_i_4970_);
v_stop_boxed_4974_ = lean_unbox_usize(v_stop_4971_);
lean_dec(v_stop_4971_);
v_res_4975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__19(v_as_4969_, v_i_boxed_4973_, v_stop_boxed_4974_, v_b_4972_);
lean_dec_ref(v_as_4969_);
return v_res_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__21(lean_object* v_opts_4976_, lean_object* v_opt_4977_){
_start:
{
lean_object* v_name_4978_; lean_object* v_defValue_4979_; lean_object* v_map_4980_; lean_object* v___x_4981_; 
v_name_4978_ = lean_ctor_get(v_opt_4977_, 0);
v_defValue_4979_ = lean_ctor_get(v_opt_4977_, 1);
v_map_4980_ = lean_ctor_get(v_opts_4976_, 0);
v___x_4981_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4980_, v_name_4978_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_inc(v_defValue_4979_);
return v_defValue_4979_;
}
else
{
lean_object* v_val_4982_; 
v_val_4982_ = lean_ctor_get(v___x_4981_, 0);
lean_inc(v_val_4982_);
lean_dec_ref_known(v___x_4981_, 1);
if (lean_obj_tag(v_val_4982_) == 3)
{
lean_object* v_v_4983_; 
v_v_4983_ = lean_ctor_get(v_val_4982_, 0);
lean_inc(v_v_4983_);
lean_dec_ref_known(v_val_4982_, 1);
return v_v_4983_;
}
else
{
lean_dec(v_val_4982_);
lean_inc(v_defValue_4979_);
return v_defValue_4979_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__21___boxed(lean_object* v_opts_4984_, lean_object* v_opt_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__21(v_opts_4984_, v_opt_4985_);
lean_dec_ref(v_opt_4985_);
lean_dec_ref(v_opts_4984_);
return v_res_4986_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg(lean_object* v_x_4987_){
_start:
{
if (lean_obj_tag(v_x_4987_) == 0)
{
lean_object* v_a_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
v_a_4989_ = lean_ctor_get(v_x_4987_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v_x_4987_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4991_ = v_x_4987_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_a_4989_);
lean_dec(v_x_4987_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
lean_ctor_set_tag(v___x_4991_, 1);
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4989_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
else
{
lean_object* v_a_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5004_; 
v_a_4997_ = lean_ctor_get(v_x_4987_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v_x_4987_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4999_ = v_x_4987_;
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_a_4997_);
lean_dec(v_x_4987_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v___x_5002_; 
if (v_isShared_5000_ == 0)
{
lean_ctor_set_tag(v___x_4999_, 0);
v___x_5002_ = v___x_4999_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_a_4997_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg___boxed(lean_object* v_x_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg(v_x_5005_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18_spec__20(size_t v_sz_5008_, size_t v_i_5009_, lean_object* v_bs_5010_){
_start:
{
uint8_t v___x_5011_; 
v___x_5011_ = lean_usize_dec_lt(v_i_5009_, v_sz_5008_);
if (v___x_5011_ == 0)
{
return v_bs_5010_;
}
else
{
lean_object* v_v_5012_; lean_object* v_msg_5013_; lean_object* v___x_5014_; lean_object* v_bs_x27_5015_; size_t v___x_5016_; size_t v___x_5017_; lean_object* v___x_5018_; 
v_v_5012_ = lean_array_uget_borrowed(v_bs_5010_, v_i_5009_);
v_msg_5013_ = lean_ctor_get(v_v_5012_, 1);
lean_inc_ref(v_msg_5013_);
v___x_5014_ = lean_unsigned_to_nat(0u);
v_bs_x27_5015_ = lean_array_uset(v_bs_5010_, v_i_5009_, v___x_5014_);
v___x_5016_ = ((size_t)1ULL);
v___x_5017_ = lean_usize_add(v_i_5009_, v___x_5016_);
v___x_5018_ = lean_array_uset(v_bs_x27_5015_, v_i_5009_, v_msg_5013_);
v_i_5009_ = v___x_5017_;
v_bs_5010_ = v___x_5018_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18_spec__20___boxed(lean_object* v_sz_5020_, lean_object* v_i_5021_, lean_object* v_bs_5022_){
_start:
{
size_t v_sz_boxed_5023_; size_t v_i_boxed_5024_; lean_object* v_res_5025_; 
v_sz_boxed_5023_ = lean_unbox_usize(v_sz_5020_);
lean_dec(v_sz_5020_);
v_i_boxed_5024_ = lean_unbox_usize(v_i_5021_);
lean_dec(v_i_5021_);
v_res_5025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18_spec__20(v_sz_boxed_5023_, v_i_boxed_5024_, v_bs_5022_);
return v_res_5025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18(lean_object* v_oldTraces_5026_, lean_object* v_data_5027_, lean_object* v_ref_5028_, lean_object* v_msg_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
lean_object* v_toCold_5035_; lean_object* v_currRecDepth_5036_; lean_object* v_ref_5037_; uint16_t v_optionFlags_5038_; uint8_t v_suppressElabErrors_5039_; uint8_t v_checkDeprecated_5040_; uint8_t v_isRecordingDeps_5041_; lean_object* v_ref_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v_traceState_5045_; lean_object* v_traces_5046_; lean_object* v___x_5047_; size_t v_sz_5048_; size_t v___x_5049_; lean_object* v___x_5050_; lean_object* v_msg_5051_; lean_object* v___x_5052_; lean_object* v_a_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5091_; 
v_toCold_5035_ = lean_ctor_get(v___y_5032_, 0);
v_currRecDepth_5036_ = lean_ctor_get(v___y_5032_, 1);
v_ref_5037_ = lean_ctor_get(v___y_5032_, 2);
v_optionFlags_5038_ = lean_ctor_get_uint16(v___y_5032_, sizeof(void*)*3);
v_suppressElabErrors_5039_ = lean_ctor_get_uint8(v___y_5032_, sizeof(void*)*3 + 2);
v_checkDeprecated_5040_ = lean_ctor_get_uint8(v___y_5032_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5041_ = lean_ctor_get_uint8(v___y_5032_, sizeof(void*)*3 + 4);
v_ref_5042_ = l_Lean_replaceRef(v_ref_5028_, v_ref_5037_);
lean_inc(v_currRecDepth_5036_);
lean_inc_ref(v_toCold_5035_);
v___x_5043_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5043_, 0, v_toCold_5035_);
lean_ctor_set(v___x_5043_, 1, v_currRecDepth_5036_);
lean_ctor_set(v___x_5043_, 2, v_ref_5042_);
lean_ctor_set_uint16(v___x_5043_, sizeof(void*)*3, v_optionFlags_5038_);
lean_ctor_set_uint8(v___x_5043_, sizeof(void*)*3 + 2, v_suppressElabErrors_5039_);
lean_ctor_set_uint8(v___x_5043_, sizeof(void*)*3 + 3, v_checkDeprecated_5040_);
lean_ctor_set_uint8(v___x_5043_, sizeof(void*)*3 + 4, v_isRecordingDeps_5041_);
v___x_5044_ = lean_st_ref_get(v___y_5033_);
v_traceState_5045_ = lean_ctor_get(v___x_5044_, 4);
lean_inc_ref(v_traceState_5045_);
lean_dec(v___x_5044_);
v_traces_5046_ = lean_ctor_get(v_traceState_5045_, 0);
lean_inc_ref(v_traces_5046_);
lean_dec_ref(v_traceState_5045_);
v___x_5047_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5046_);
lean_dec_ref(v_traces_5046_);
v_sz_5048_ = lean_array_size(v___x_5047_);
v___x_5049_ = ((size_t)0ULL);
v___x_5050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18_spec__20(v_sz_5048_, v___x_5049_, v___x_5047_);
v_msg_5051_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5051_, 0, v_data_5027_);
lean_ctor_set(v_msg_5051_, 1, v_msg_5029_);
lean_ctor_set(v_msg_5051_, 2, v___x_5050_);
v___x_5052_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5_spec__8(v_msg_5051_, v___y_5030_, v___y_5031_, v___x_5043_, v___y_5033_);
lean_dec_ref_known(v___x_5043_, 3);
v_a_5053_ = lean_ctor_get(v___x_5052_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5052_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5055_ = v___x_5052_;
v_isShared_5056_ = v_isSharedCheck_5091_;
goto v_resetjp_5054_;
}
else
{
lean_inc(v_a_5053_);
lean_dec(v___x_5052_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5091_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
lean_object* v___x_5057_; lean_object* v_traceState_5058_; lean_object* v_env_5059_; lean_object* v_nextMacroScope_5060_; lean_object* v_ngen_5061_; lean_object* v_auxDeclNGen_5062_; lean_object* v_cache_5063_; lean_object* v_recordedDeps_5064_; lean_object* v_messages_5065_; lean_object* v_infoState_5066_; lean_object* v_snapshotTasks_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5090_; 
v___x_5057_ = lean_st_ref_take(v___y_5033_);
v_traceState_5058_ = lean_ctor_get(v___x_5057_, 4);
v_env_5059_ = lean_ctor_get(v___x_5057_, 0);
v_nextMacroScope_5060_ = lean_ctor_get(v___x_5057_, 1);
v_ngen_5061_ = lean_ctor_get(v___x_5057_, 2);
v_auxDeclNGen_5062_ = lean_ctor_get(v___x_5057_, 3);
v_cache_5063_ = lean_ctor_get(v___x_5057_, 5);
v_recordedDeps_5064_ = lean_ctor_get(v___x_5057_, 6);
v_messages_5065_ = lean_ctor_get(v___x_5057_, 7);
v_infoState_5066_ = lean_ctor_get(v___x_5057_, 8);
v_snapshotTasks_5067_ = lean_ctor_get(v___x_5057_, 9);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5069_ = v___x_5057_;
v_isShared_5070_ = v_isSharedCheck_5090_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_snapshotTasks_5067_);
lean_inc(v_infoState_5066_);
lean_inc(v_messages_5065_);
lean_inc(v_recordedDeps_5064_);
lean_inc(v_cache_5063_);
lean_inc(v_traceState_5058_);
lean_inc(v_auxDeclNGen_5062_);
lean_inc(v_ngen_5061_);
lean_inc(v_nextMacroScope_5060_);
lean_inc(v_env_5059_);
lean_dec(v___x_5057_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5090_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
uint64_t v_tid_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5088_; 
v_tid_5071_ = lean_ctor_get_uint64(v_traceState_5058_, sizeof(void*)*1);
v_isSharedCheck_5088_ = !lean_is_exclusive(v_traceState_5058_);
if (v_isSharedCheck_5088_ == 0)
{
lean_object* v_unused_5089_; 
v_unused_5089_ = lean_ctor_get(v_traceState_5058_, 0);
lean_dec(v_unused_5089_);
v___x_5073_ = v_traceState_5058_;
v_isShared_5074_ = v_isSharedCheck_5088_;
goto v_resetjp_5072_;
}
else
{
lean_dec(v_traceState_5058_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5088_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5079_; 
v___x_5075_ = lean_box(0);
v___x_5076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5076_, 0, v_ref_5028_);
lean_ctor_set(v___x_5076_, 1, v_a_5053_);
v___x_5077_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5026_, v___x_5076_);
if (v_isShared_5074_ == 0)
{
lean_ctor_set(v___x_5073_, 0, v___x_5077_);
v___x_5079_ = v___x_5073_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v___x_5077_);
lean_ctor_set_uint64(v_reuseFailAlloc_5087_, sizeof(void*)*1, v_tid_5071_);
v___x_5079_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
lean_object* v___x_5081_; 
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 4, v___x_5079_);
v___x_5081_ = v___x_5069_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_env_5059_);
lean_ctor_set(v_reuseFailAlloc_5086_, 1, v_nextMacroScope_5060_);
lean_ctor_set(v_reuseFailAlloc_5086_, 2, v_ngen_5061_);
lean_ctor_set(v_reuseFailAlloc_5086_, 3, v_auxDeclNGen_5062_);
lean_ctor_set(v_reuseFailAlloc_5086_, 4, v___x_5079_);
lean_ctor_set(v_reuseFailAlloc_5086_, 5, v_cache_5063_);
lean_ctor_set(v_reuseFailAlloc_5086_, 6, v_recordedDeps_5064_);
lean_ctor_set(v_reuseFailAlloc_5086_, 7, v_messages_5065_);
lean_ctor_set(v_reuseFailAlloc_5086_, 8, v_infoState_5066_);
lean_ctor_set(v_reuseFailAlloc_5086_, 9, v_snapshotTasks_5067_);
v___x_5081_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
lean_object* v___x_5082_; lean_object* v___x_5084_; 
v___x_5082_ = lean_st_ref_put(v___y_5033_, v___x_5081_);
if (v_isShared_5056_ == 0)
{
lean_ctor_set(v___x_5055_, 0, v___x_5075_);
v___x_5084_ = v___x_5055_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5075_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18___boxed(lean_object* v_oldTraces_5092_, lean_object* v_data_5093_, lean_object* v_ref_5094_, lean_object* v_msg_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18(v_oldTraces_5092_, v_data_5093_, v_ref_5094_, v_msg_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_);
lean_dec(v___y_5099_);
lean_dec_ref(v___y_5098_);
lean_dec(v___y_5097_);
lean_dec_ref(v___y_5096_);
return v_res_5101_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__20(lean_object* v_e_5102_){
_start:
{
if (lean_obj_tag(v_e_5102_) == 0)
{
uint8_t v___x_5103_; 
v___x_5103_ = 2;
return v___x_5103_;
}
else
{
uint8_t v___x_5104_; 
v___x_5104_ = 0;
return v___x_5104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__20___boxed(lean_object* v_e_5105_){
_start:
{
uint8_t v_res_5106_; lean_object* v_r_5107_; 
v_res_5106_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__20(v_e_5105_);
lean_dec_ref(v_e_5105_);
v_r_5107_ = lean_box(v_res_5106_);
return v_r_5107_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__1(void){
_start:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5109_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__0));
v___x_5110_ = l_Lean_stringToMessageData(v___x_5109_);
return v___x_5110_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__2(void){
_start:
{
lean_object* v___x_5111_; double v___x_5112_; 
v___x_5111_ = lean_unsigned_to_nat(1000u);
v___x_5112_ = lean_float_of_nat(v___x_5111_);
return v___x_5112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16(lean_object* v_cls_5113_, uint8_t v_collapsed_5114_, lean_object* v_tag_5115_, lean_object* v_opts_5116_, uint8_t v_clsEnabled_5117_, lean_object* v_oldTraces_5118_, lean_object* v_msg_5119_, lean_object* v_resStartStop_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_){
_start:
{
lean_object* v_fst_5126_; lean_object* v_snd_5127_; lean_object* v___y_5129_; lean_object* v___y_5130_; lean_object* v_data_5131_; lean_object* v_fst_5134_; lean_object* v_snd_5135_; lean_object* v___x_5136_; uint8_t v___x_5137_; lean_object* v___y_5139_; lean_object* v_a_5140_; uint8_t v___y_5155_; double v___y_5187_; 
v_fst_5126_ = lean_ctor_get(v_resStartStop_5120_, 0);
lean_inc(v_fst_5126_);
v_snd_5127_ = lean_ctor_get(v_resStartStop_5120_, 1);
lean_inc(v_snd_5127_);
lean_dec_ref(v_resStartStop_5120_);
v_fst_5134_ = lean_ctor_get(v_snd_5127_, 0);
lean_inc(v_fst_5134_);
v_snd_5135_ = lean_ctor_get(v_snd_5127_, 1);
lean_inc(v_snd_5135_);
lean_dec(v_snd_5127_);
v___x_5136_ = l_Lean_trace_profiler;
v___x_5137_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15(v_opts_5116_, v___x_5136_);
if (v___x_5137_ == 0)
{
v___y_5155_ = v___x_5137_;
goto v___jp_5154_;
}
else
{
lean_object* v___x_5192_; uint8_t v___x_5193_; 
v___x_5192_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5193_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15(v_opts_5116_, v___x_5192_);
if (v___x_5193_ == 0)
{
lean_object* v___x_5194_; lean_object* v___x_5195_; double v___x_5196_; double v___x_5197_; double v___x_5198_; 
v___x_5194_ = l_Lean_trace_profiler_threshold;
v___x_5195_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__21(v_opts_5116_, v___x_5194_);
v___x_5196_ = lean_float_of_nat(v___x_5195_);
v___x_5197_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__2);
v___x_5198_ = lean_float_div(v___x_5196_, v___x_5197_);
v___y_5187_ = v___x_5198_;
goto v___jp_5186_;
}
else
{
lean_object* v___x_5199_; lean_object* v___x_5200_; double v___x_5201_; 
v___x_5199_ = l_Lean_trace_profiler_threshold;
v___x_5200_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__21(v_opts_5116_, v___x_5199_);
v___x_5201_ = lean_float_of_nat(v___x_5200_);
v___y_5187_ = v___x_5201_;
goto v___jp_5186_;
}
}
v___jp_5128_:
{
lean_object* v___x_5132_; 
lean_inc(v___y_5130_);
v___x_5132_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__18(v_oldTraces_5118_, v_data_5131_, v___y_5130_, v___y_5129_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v___x_5133_; 
lean_dec_ref_known(v___x_5132_, 1);
v___x_5133_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg(v_fst_5126_);
return v___x_5133_;
}
else
{
lean_dec(v_fst_5126_);
return v___x_5132_;
}
}
v___jp_5138_:
{
uint8_t v_result_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; double v___x_5144_; lean_object* v_data_5145_; 
v_result_5141_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__20(v_fst_5126_);
v___x_5142_ = lean_box(v_result_5141_);
v___x_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5143_, 0, v___x_5142_);
v___x_5144_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0);
lean_inc_ref(v_tag_5115_);
lean_inc_ref(v___x_5143_);
lean_inc(v_cls_5113_);
v_data_5145_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5145_, 0, v_cls_5113_);
lean_ctor_set(v_data_5145_, 1, v___x_5143_);
lean_ctor_set(v_data_5145_, 2, v_tag_5115_);
lean_ctor_set_float(v_data_5145_, sizeof(void*)*3, v___x_5144_);
lean_ctor_set_float(v_data_5145_, sizeof(void*)*3 + 8, v___x_5144_);
lean_ctor_set_uint8(v_data_5145_, sizeof(void*)*3 + 16, v_collapsed_5114_);
if (v___x_5137_ == 0)
{
lean_dec_ref_known(v___x_5143_, 1);
lean_dec(v_snd_5135_);
lean_dec(v_fst_5134_);
lean_dec_ref(v_tag_5115_);
lean_dec(v_cls_5113_);
v___y_5129_ = v_a_5140_;
v___y_5130_ = v___y_5139_;
v_data_5131_ = v_data_5145_;
goto v___jp_5128_;
}
else
{
lean_object* v_data_5146_; double v___x_5147_; double v___x_5148_; 
lean_dec_ref_known(v_data_5145_, 3);
v_data_5146_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5146_, 0, v_cls_5113_);
lean_ctor_set(v_data_5146_, 1, v___x_5143_);
lean_ctor_set(v_data_5146_, 2, v_tag_5115_);
v___x_5147_ = lean_unbox_float(v_fst_5134_);
lean_dec(v_fst_5134_);
lean_ctor_set_float(v_data_5146_, sizeof(void*)*3, v___x_5147_);
v___x_5148_ = lean_unbox_float(v_snd_5135_);
lean_dec(v_snd_5135_);
lean_ctor_set_float(v_data_5146_, sizeof(void*)*3 + 8, v___x_5148_);
lean_ctor_set_uint8(v_data_5146_, sizeof(void*)*3 + 16, v_collapsed_5114_);
v___y_5129_ = v_a_5140_;
v___y_5130_ = v___y_5139_;
v_data_5131_ = v_data_5146_;
goto v___jp_5128_;
}
}
v___jp_5149_:
{
lean_object* v_ref_5150_; lean_object* v___x_5151_; 
v_ref_5150_ = lean_ctor_get(v___y_5123_, 2);
lean_inc(v___y_5124_);
lean_inc_ref(v___y_5123_);
lean_inc(v___y_5122_);
lean_inc_ref(v___y_5121_);
lean_inc(v_fst_5126_);
v___x_5151_ = lean_apply_6(v_msg_5119_, v_fst_5126_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, lean_box(0));
if (lean_obj_tag(v___x_5151_) == 0)
{
lean_object* v_a_5152_; 
v_a_5152_ = lean_ctor_get(v___x_5151_, 0);
lean_inc(v_a_5152_);
lean_dec_ref_known(v___x_5151_, 1);
v___y_5139_ = v_ref_5150_;
v_a_5140_ = v_a_5152_;
goto v___jp_5138_;
}
else
{
lean_object* v___x_5153_; 
lean_dec_ref_known(v___x_5151_, 1);
v___x_5153_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___closed__1);
v___y_5139_ = v_ref_5150_;
v_a_5140_ = v___x_5153_;
goto v___jp_5138_;
}
}
v___jp_5154_:
{
if (v_clsEnabled_5117_ == 0)
{
if (v___y_5155_ == 0)
{
lean_object* v___x_5156_; lean_object* v_traceState_5157_; lean_object* v_env_5158_; lean_object* v_nextMacroScope_5159_; lean_object* v_ngen_5160_; lean_object* v_auxDeclNGen_5161_; lean_object* v_cache_5162_; lean_object* v_recordedDeps_5163_; lean_object* v_messages_5164_; lean_object* v_infoState_5165_; lean_object* v_snapshotTasks_5166_; lean_object* v___x_5168_; uint8_t v_isShared_5169_; uint8_t v_isSharedCheck_5185_; 
lean_dec(v_snd_5135_);
lean_dec(v_fst_5134_);
lean_dec_ref(v_msg_5119_);
lean_dec_ref(v_tag_5115_);
lean_dec(v_cls_5113_);
v___x_5156_ = lean_st_ref_take(v___y_5124_);
v_traceState_5157_ = lean_ctor_get(v___x_5156_, 4);
v_env_5158_ = lean_ctor_get(v___x_5156_, 0);
v_nextMacroScope_5159_ = lean_ctor_get(v___x_5156_, 1);
v_ngen_5160_ = lean_ctor_get(v___x_5156_, 2);
v_auxDeclNGen_5161_ = lean_ctor_get(v___x_5156_, 3);
v_cache_5162_ = lean_ctor_get(v___x_5156_, 5);
v_recordedDeps_5163_ = lean_ctor_get(v___x_5156_, 6);
v_messages_5164_ = lean_ctor_get(v___x_5156_, 7);
v_infoState_5165_ = lean_ctor_get(v___x_5156_, 8);
v_snapshotTasks_5166_ = lean_ctor_get(v___x_5156_, 9);
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_5156_);
if (v_isSharedCheck_5185_ == 0)
{
v___x_5168_ = v___x_5156_;
v_isShared_5169_ = v_isSharedCheck_5185_;
goto v_resetjp_5167_;
}
else
{
lean_inc(v_snapshotTasks_5166_);
lean_inc(v_infoState_5165_);
lean_inc(v_messages_5164_);
lean_inc(v_recordedDeps_5163_);
lean_inc(v_cache_5162_);
lean_inc(v_traceState_5157_);
lean_inc(v_auxDeclNGen_5161_);
lean_inc(v_ngen_5160_);
lean_inc(v_nextMacroScope_5159_);
lean_inc(v_env_5158_);
lean_dec(v___x_5156_);
v___x_5168_ = lean_box(0);
v_isShared_5169_ = v_isSharedCheck_5185_;
goto v_resetjp_5167_;
}
v_resetjp_5167_:
{
uint64_t v_tid_5170_; lean_object* v_traces_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5184_; 
v_tid_5170_ = lean_ctor_get_uint64(v_traceState_5157_, sizeof(void*)*1);
v_traces_5171_ = lean_ctor_get(v_traceState_5157_, 0);
v_isSharedCheck_5184_ = !lean_is_exclusive(v_traceState_5157_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5173_ = v_traceState_5157_;
v_isShared_5174_ = v_isSharedCheck_5184_;
goto v_resetjp_5172_;
}
else
{
lean_inc(v_traces_5171_);
lean_dec(v_traceState_5157_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5184_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
lean_object* v___x_5175_; lean_object* v___x_5177_; 
v___x_5175_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5118_, v_traces_5171_);
lean_dec_ref(v_traces_5171_);
if (v_isShared_5174_ == 0)
{
lean_ctor_set(v___x_5173_, 0, v___x_5175_);
v___x_5177_ = v___x_5173_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v___x_5175_);
lean_ctor_set_uint64(v_reuseFailAlloc_5183_, sizeof(void*)*1, v_tid_5170_);
v___x_5177_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
lean_object* v___x_5179_; 
if (v_isShared_5169_ == 0)
{
lean_ctor_set(v___x_5168_, 4, v___x_5177_);
v___x_5179_ = v___x_5168_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_env_5158_);
lean_ctor_set(v_reuseFailAlloc_5182_, 1, v_nextMacroScope_5159_);
lean_ctor_set(v_reuseFailAlloc_5182_, 2, v_ngen_5160_);
lean_ctor_set(v_reuseFailAlloc_5182_, 3, v_auxDeclNGen_5161_);
lean_ctor_set(v_reuseFailAlloc_5182_, 4, v___x_5177_);
lean_ctor_set(v_reuseFailAlloc_5182_, 5, v_cache_5162_);
lean_ctor_set(v_reuseFailAlloc_5182_, 6, v_recordedDeps_5163_);
lean_ctor_set(v_reuseFailAlloc_5182_, 7, v_messages_5164_);
lean_ctor_set(v_reuseFailAlloc_5182_, 8, v_infoState_5165_);
lean_ctor_set(v_reuseFailAlloc_5182_, 9, v_snapshotTasks_5166_);
v___x_5179_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
lean_object* v___x_5180_; lean_object* v___x_5181_; 
v___x_5180_ = lean_st_ref_put(v___y_5124_, v___x_5179_);
v___x_5181_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg(v_fst_5126_);
return v___x_5181_;
}
}
}
}
}
else
{
goto v___jp_5149_;
}
}
else
{
goto v___jp_5149_;
}
}
v___jp_5186_:
{
double v___x_5188_; double v___x_5189_; double v___x_5190_; uint8_t v___x_5191_; 
v___x_5188_ = lean_unbox_float(v_snd_5135_);
v___x_5189_ = lean_unbox_float(v_fst_5134_);
v___x_5190_ = lean_float_sub(v___x_5188_, v___x_5189_);
v___x_5191_ = lean_float_decLt(v___y_5187_, v___x_5190_);
v___y_5155_ = v___x_5191_;
goto v___jp_5154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16___boxed(lean_object* v_cls_5202_, lean_object* v_collapsed_5203_, lean_object* v_tag_5204_, lean_object* v_opts_5205_, lean_object* v_clsEnabled_5206_, lean_object* v_oldTraces_5207_, lean_object* v_msg_5208_, lean_object* v_resStartStop_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_){
_start:
{
uint8_t v_collapsed_boxed_5215_; uint8_t v_clsEnabled_boxed_5216_; lean_object* v_res_5217_; 
v_collapsed_boxed_5215_ = lean_unbox(v_collapsed_5203_);
v_clsEnabled_boxed_5216_ = lean_unbox(v_clsEnabled_5206_);
v_res_5217_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16(v_cls_5202_, v_collapsed_boxed_5215_, v_tag_5204_, v_opts_5205_, v_clsEnabled_boxed_5216_, v_oldTraces_5207_, v_msg_5208_, v_resStartStop_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
lean_dec(v___y_5213_);
lean_dec_ref(v___y_5212_);
lean_dec(v___y_5211_);
lean_dec_ref(v___y_5210_);
lean_dec_ref(v_opts_5205_);
return v_res_5217_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__1(void){
_start:
{
lean_object* v___x_5219_; double v___x_5220_; 
v___x_5219_ = lean_unsigned_to_nat(1000000000u);
v___x_5220_ = lean_float_of_nat(v___x_5219_);
return v___x_5220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem(lean_object* v_problem_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_){
_start:
{
lean_object* v_sortInfo_5227_; lean_object* v_predInfo_5228_; lean_object* v_groundFacts_5229_; lean_object* v_quantifiedFacts_5230_; lean_object* v___y_5232_; size_t v___y_5233_; lean_object* v___y_5234_; lean_object* v___y_5250_; lean_object* v___y_5251_; size_t v___y_5252_; lean_object* v___y_5253_; lean_object* v___y_5254_; lean_object* v___y_5255_; lean_object* v___y_5258_; lean_object* v___y_5259_; size_t v___y_5260_; lean_object* v___y_5261_; lean_object* v___y_5262_; lean_object* v___y_5263_; lean_object* v___y_5266_; lean_object* v___y_5267_; lean_object* v___y_5268_; size_t v___y_5269_; lean_object* v___y_5270_; lean_object* v___y_5276_; size_t v___y_5277_; lean_object* v___y_5278_; lean_object* v___y_5294_; lean_object* v___y_5295_; lean_object* v___y_5296_; lean_object* v___y_5297_; size_t v___y_5298_; lean_object* v___y_5299_; lean_object* v___y_5302_; lean_object* v___y_5303_; lean_object* v___y_5304_; lean_object* v___y_5305_; size_t v___y_5306_; lean_object* v___y_5307_; lean_object* v___y_5310_; lean_object* v___y_5311_; lean_object* v___y_5312_; size_t v___y_5313_; lean_object* v___y_5314_; lean_object* v_size_5319_; lean_object* v_buckets_5320_; lean_object* v___f_5321_; lean_object* v_cls_5322_; uint8_t v___y_5324_; lean_object* v___y_5325_; uint8_t v___y_5326_; lean_object* v___y_5327_; lean_object* v___y_5328_; lean_object* v___y_5329_; lean_object* v_a_5330_; lean_object* v___y_5340_; uint8_t v___y_5341_; uint8_t v___y_5342_; lean_object* v___y_5343_; lean_object* v___y_5344_; lean_object* v___y_5345_; lean_object* v_a_5346_; lean_object* v___y_5349_; lean_object* v___y_5350_; uint8_t v___y_5351_; uint8_t v___y_5352_; lean_object* v___y_5353_; lean_object* v___y_5354_; size_t v___y_5355_; lean_object* v___y_5356_; lean_object* v___y_5357_; lean_object* v___y_5376_; uint8_t v___y_5377_; lean_object* v___y_5378_; uint8_t v___y_5379_; lean_object* v___y_5380_; lean_object* v___y_5381_; lean_object* v___y_5382_; size_t v___y_5383_; lean_object* v___y_5384_; lean_object* v___y_5385_; lean_object* v___y_5386_; lean_object* v___y_5387_; lean_object* v___y_5390_; lean_object* v___y_5391_; uint8_t v___y_5392_; uint8_t v___y_5393_; lean_object* v___y_5394_; lean_object* v___y_5395_; lean_object* v___y_5396_; size_t v___y_5397_; lean_object* v___y_5398_; lean_object* v___y_5399_; lean_object* v___y_5400_; lean_object* v___y_5401_; lean_object* v___y_5404_; uint8_t v___y_5405_; lean_object* v___y_5406_; uint8_t v___y_5407_; lean_object* v___y_5408_; lean_object* v___y_5409_; lean_object* v___y_5410_; lean_object* v___y_5411_; size_t v___y_5412_; lean_object* v___y_5413_; lean_object* v___y_5414_; uint8_t v___y_5420_; lean_object* v___y_5421_; uint8_t v___y_5422_; lean_object* v___y_5423_; lean_object* v___y_5424_; lean_object* v___y_5425_; lean_object* v_a_5426_; lean_object* v___y_5439_; uint8_t v___y_5440_; uint8_t v___y_5441_; lean_object* v___y_5442_; lean_object* v___y_5443_; lean_object* v___y_5444_; lean_object* v_a_5445_; lean_object* v___y_5448_; lean_object* v___y_5449_; uint8_t v___y_5450_; uint8_t v___y_5451_; lean_object* v___y_5452_; lean_object* v___y_5453_; size_t v___y_5454_; lean_object* v___y_5455_; lean_object* v___y_5456_; lean_object* v___y_5475_; uint8_t v___y_5476_; lean_object* v___y_5477_; uint8_t v___y_5478_; lean_object* v___y_5479_; lean_object* v___y_5480_; lean_object* v___y_5481_; lean_object* v___y_5482_; size_t v___y_5483_; lean_object* v___y_5484_; lean_object* v___y_5485_; lean_object* v___y_5486_; lean_object* v___y_5489_; lean_object* v___y_5490_; uint8_t v___y_5491_; lean_object* v___y_5492_; uint8_t v___y_5493_; lean_object* v___y_5494_; lean_object* v___y_5495_; lean_object* v___y_5496_; size_t v___y_5497_; lean_object* v___y_5498_; lean_object* v___y_5499_; lean_object* v___y_5500_; lean_object* v___y_5503_; uint8_t v___y_5504_; lean_object* v___y_5505_; uint8_t v___y_5506_; lean_object* v___y_5507_; lean_object* v___y_5508_; lean_object* v___y_5509_; lean_object* v___y_5510_; size_t v___y_5511_; lean_object* v___y_5512_; lean_object* v___y_5513_; size_t v___y_5519_; lean_object* v___y_5520_; uint8_t v___y_5521_; lean_object* v___y_5522_; uint8_t v___y_5523_; lean_object* v___y_5524_; lean_object* v___y_5525_; lean_object* v___y_5526_; lean_object* v___y_5527_; size_t v___y_5528_; lean_object* v___y_5554_; lean_object* v___y_5555_; lean_object* v___y_5556_; lean_object* v___y_5586_; lean_object* v___y_5587_; lean_object* v___y_5588_; lean_object* v___y_5589_; lean_object* v___y_5590_; lean_object* v___y_5591_; lean_object* v___y_5594_; lean_object* v___y_5595_; lean_object* v___y_5596_; lean_object* v___y_5597_; lean_object* v___y_5598_; lean_object* v___y_5599_; lean_object* v___y_5602_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; uint8_t v___x_5612_; 
v_sortInfo_5227_ = lean_ctor_get(v_problem_5221_, 0);
v_predInfo_5228_ = lean_ctor_get(v_problem_5221_, 2);
v_groundFacts_5229_ = lean_ctor_get(v_problem_5221_, 3);
v_quantifiedFacts_5230_ = lean_ctor_get(v_problem_5221_, 4);
v_size_5319_ = lean_ctor_get(v_sortInfo_5227_, 0);
v_buckets_5320_ = lean_ctor_get(v_sortInfo_5227_, 1);
v___f_5321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__0));
v_cls_5322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__6));
v___x_5609_ = lean_mk_empty_array_with_capacity(v_size_5319_);
v___x_5610_ = lean_unsigned_to_nat(0u);
v___x_5611_ = lean_array_get_size(v_buckets_5320_);
v___x_5612_ = lean_nat_dec_lt(v___x_5610_, v___x_5611_);
if (v___x_5612_ == 0)
{
v___y_5602_ = v___x_5609_;
goto v___jp_5601_;
}
else
{
size_t v___x_5613_; size_t v___x_5614_; lean_object* v___x_5615_; 
v___x_5613_ = ((size_t)0ULL);
v___x_5614_ = lean_usize_of_nat(v___x_5611_);
v___x_5615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__19(v_buckets_5320_, v___x_5613_, v___x_5614_, v___x_5609_);
v___y_5602_ = v___x_5615_;
goto v___jp_5601_;
}
v___jp_5231_:
{
size_t v_sz_5235_; lean_object* v___x_5236_; 
v_sz_5235_ = lean_array_size(v___y_5234_);
v___x_5236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8(v_sortInfo_5227_, v___y_5234_, v_sz_5235_, v___y_5233_, v___y_5232_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
lean_dec_ref(v___y_5234_);
if (lean_obj_tag(v___x_5236_) == 0)
{
size_t v_sz_5237_; lean_object* v___x_5238_; 
lean_dec_ref_known(v___x_5236_, 1);
v_sz_5237_ = lean_array_size(v_groundFacts_5229_);
v___x_5238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9(v_groundFacts_5229_, v_sz_5237_, v___y_5233_, v___y_5232_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
if (lean_obj_tag(v___x_5238_) == 0)
{
size_t v_sz_5239_; lean_object* v___x_5240_; 
lean_dec_ref_known(v___x_5238_, 1);
v_sz_5239_ = lean_array_size(v_quantifiedFacts_5230_);
v___x_5240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10(v_quantifiedFacts_5230_, v_sz_5239_, v___y_5233_, v___y_5232_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
if (lean_obj_tag(v___x_5240_) == 0)
{
lean_object* v___x_5242_; uint8_t v_isShared_5243_; uint8_t v_isSharedCheck_5247_; 
v_isSharedCheck_5247_ = !lean_is_exclusive(v___x_5240_);
if (v_isSharedCheck_5247_ == 0)
{
lean_object* v_unused_5248_; 
v_unused_5248_ = lean_ctor_get(v___x_5240_, 0);
lean_dec(v_unused_5248_);
v___x_5242_ = v___x_5240_;
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
else
{
lean_dec(v___x_5240_);
v___x_5242_ = lean_box(0);
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
v_resetjp_5241_:
{
lean_object* v___x_5245_; 
if (v_isShared_5243_ == 0)
{
lean_ctor_set(v___x_5242_, 0, v___y_5232_);
v___x_5245_ = v___x_5242_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v___y_5232_);
v___x_5245_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
return v___x_5245_;
}
}
}
else
{
return v___x_5240_;
}
}
else
{
return v___x_5238_;
}
}
else
{
return v___x_5236_;
}
}
v___jp_5249_:
{
lean_object* v___x_5256_; 
v___x_5256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v___y_5251_, v___y_5254_, v___y_5253_, v___y_5255_);
lean_dec(v___y_5255_);
lean_dec(v___y_5251_);
v___y_5232_ = v___y_5250_;
v___y_5233_ = v___y_5252_;
v___y_5234_ = v___x_5256_;
goto v___jp_5231_;
}
v___jp_5257_:
{
uint8_t v___x_5264_; 
v___x_5264_ = lean_nat_dec_le(v___y_5263_, v___y_5261_);
if (v___x_5264_ == 0)
{
lean_dec(v___y_5261_);
lean_inc(v___y_5263_);
v___y_5250_ = v___y_5258_;
v___y_5251_ = v___y_5259_;
v___y_5252_ = v___y_5260_;
v___y_5253_ = v___y_5263_;
v___y_5254_ = v___y_5262_;
v___y_5255_ = v___y_5263_;
goto v___jp_5249_;
}
else
{
v___y_5250_ = v___y_5258_;
v___y_5251_ = v___y_5259_;
v___y_5252_ = v___y_5260_;
v___y_5253_ = v___y_5263_;
v___y_5254_ = v___y_5262_;
v___y_5255_ = v___y_5261_;
goto v___jp_5249_;
}
}
v___jp_5265_:
{
lean_object* v___x_5271_; uint8_t v___x_5272_; 
v___x_5271_ = lean_array_get_size(v___y_5270_);
v___x_5272_ = lean_nat_dec_eq(v___x_5271_, v___y_5267_);
if (v___x_5272_ == 0)
{
lean_object* v___x_5273_; uint8_t v___x_5274_; 
v___x_5273_ = lean_nat_sub(v___x_5271_, v___y_5268_);
v___x_5274_ = lean_nat_dec_le(v___y_5267_, v___x_5273_);
if (v___x_5274_ == 0)
{
lean_dec(v___y_5267_);
lean_inc(v___x_5273_);
v___y_5258_ = v___y_5266_;
v___y_5259_ = v___x_5271_;
v___y_5260_ = v___y_5269_;
v___y_5261_ = v___x_5273_;
v___y_5262_ = v___y_5270_;
v___y_5263_ = v___x_5273_;
goto v___jp_5257_;
}
else
{
v___y_5258_ = v___y_5266_;
v___y_5259_ = v___x_5271_;
v___y_5260_ = v___y_5269_;
v___y_5261_ = v___x_5273_;
v___y_5262_ = v___y_5270_;
v___y_5263_ = v___y_5267_;
goto v___jp_5257_;
}
}
else
{
lean_dec(v___y_5267_);
v___y_5232_ = v___y_5266_;
v___y_5233_ = v___y_5269_;
v___y_5234_ = v___y_5270_;
goto v___jp_5231_;
}
}
v___jp_5275_:
{
size_t v_sz_5279_; lean_object* v___x_5280_; 
v_sz_5279_ = lean_array_size(v___y_5278_);
v___x_5280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8(v_sortInfo_5227_, v___y_5278_, v_sz_5279_, v___y_5277_, v___y_5276_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
lean_dec_ref(v___y_5278_);
if (lean_obj_tag(v___x_5280_) == 0)
{
size_t v_sz_5281_; lean_object* v___x_5282_; 
lean_dec_ref_known(v___x_5280_, 1);
v_sz_5281_ = lean_array_size(v_groundFacts_5229_);
v___x_5282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9(v_groundFacts_5229_, v_sz_5281_, v___y_5277_, v___y_5276_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
if (lean_obj_tag(v___x_5282_) == 0)
{
size_t v_sz_5283_; lean_object* v___x_5284_; 
lean_dec_ref_known(v___x_5282_, 1);
v_sz_5283_ = lean_array_size(v_quantifiedFacts_5230_);
v___x_5284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10(v_quantifiedFacts_5230_, v_sz_5283_, v___y_5277_, v___y_5276_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
if (lean_obj_tag(v___x_5284_) == 0)
{
lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5291_; 
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5291_ == 0)
{
lean_object* v_unused_5292_; 
v_unused_5292_ = lean_ctor_get(v___x_5284_, 0);
lean_dec(v_unused_5292_);
v___x_5286_ = v___x_5284_;
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
else
{
lean_dec(v___x_5284_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___x_5289_; 
if (v_isShared_5287_ == 0)
{
lean_ctor_set(v___x_5286_, 0, v___y_5276_);
v___x_5289_ = v___x_5286_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v___y_5276_);
v___x_5289_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
return v___x_5289_;
}
}
}
else
{
return v___x_5284_;
}
}
else
{
return v___x_5282_;
}
}
else
{
return v___x_5280_;
}
}
v___jp_5293_:
{
lean_object* v___x_5300_; 
v___x_5300_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v___y_5295_, v___y_5296_, v___y_5297_, v___y_5299_);
lean_dec(v___y_5299_);
lean_dec(v___y_5295_);
v___y_5276_ = v___y_5294_;
v___y_5277_ = v___y_5298_;
v___y_5278_ = v___x_5300_;
goto v___jp_5275_;
}
v___jp_5301_:
{
uint8_t v___x_5308_; 
v___x_5308_ = lean_nat_dec_le(v___y_5307_, v___y_5302_);
if (v___x_5308_ == 0)
{
lean_dec(v___y_5302_);
lean_inc(v___y_5307_);
v___y_5294_ = v___y_5303_;
v___y_5295_ = v___y_5304_;
v___y_5296_ = v___y_5305_;
v___y_5297_ = v___y_5307_;
v___y_5298_ = v___y_5306_;
v___y_5299_ = v___y_5307_;
goto v___jp_5293_;
}
else
{
v___y_5294_ = v___y_5303_;
v___y_5295_ = v___y_5304_;
v___y_5296_ = v___y_5305_;
v___y_5297_ = v___y_5307_;
v___y_5298_ = v___y_5306_;
v___y_5299_ = v___y_5302_;
goto v___jp_5293_;
}
}
v___jp_5309_:
{
lean_object* v___x_5315_; uint8_t v___x_5316_; 
v___x_5315_ = lean_array_get_size(v___y_5314_);
v___x_5316_ = lean_nat_dec_eq(v___x_5315_, v___y_5311_);
if (v___x_5316_ == 0)
{
lean_object* v___x_5317_; uint8_t v___x_5318_; 
v___x_5317_ = lean_nat_sub(v___x_5315_, v___y_5312_);
v___x_5318_ = lean_nat_dec_le(v___y_5311_, v___x_5317_);
if (v___x_5318_ == 0)
{
lean_dec(v___y_5311_);
lean_inc(v___x_5317_);
v___y_5302_ = v___x_5317_;
v___y_5303_ = v___y_5310_;
v___y_5304_ = v___x_5315_;
v___y_5305_ = v___y_5314_;
v___y_5306_ = v___y_5313_;
v___y_5307_ = v___x_5317_;
goto v___jp_5301_;
}
else
{
v___y_5302_ = v___x_5317_;
v___y_5303_ = v___y_5310_;
v___y_5304_ = v___x_5315_;
v___y_5305_ = v___y_5314_;
v___y_5306_ = v___y_5313_;
v___y_5307_ = v___y_5311_;
goto v___jp_5301_;
}
}
else
{
lean_dec(v___y_5311_);
v___y_5276_ = v___y_5310_;
v___y_5277_ = v___y_5313_;
v___y_5278_ = v___y_5314_;
goto v___jp_5275_;
}
}
v___jp_5323_:
{
lean_object* v___x_5331_; double v___x_5332_; double v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; 
v___x_5331_ = lean_io_get_num_heartbeats();
v___x_5332_ = lean_float_of_nat(v___y_5329_);
v___x_5333_ = lean_float_of_nat(v___x_5331_);
v___x_5334_ = lean_box_float(v___x_5332_);
v___x_5335_ = lean_box_float(v___x_5333_);
v___x_5336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5336_, 0, v___x_5334_);
lean_ctor_set(v___x_5336_, 1, v___x_5335_);
v___x_5337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5337_, 0, v_a_5330_);
lean_ctor_set(v___x_5337_, 1, v___x_5336_);
lean_inc_ref(v___y_5328_);
v___x_5338_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16(v_cls_5322_, v___y_5326_, v___y_5328_, v___y_5325_, v___y_5324_, v___y_5327_, v___f_5321_, v___x_5337_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
return v___x_5338_;
}
v___jp_5339_:
{
lean_object* v___x_5347_; 
v___x_5347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5347_, 0, v_a_5346_);
v___y_5324_ = v___y_5341_;
v___y_5325_ = v___y_5340_;
v___y_5326_ = v___y_5342_;
v___y_5327_ = v___y_5344_;
v___y_5328_ = v___y_5343_;
v___y_5329_ = v___y_5345_;
v_a_5330_ = v___x_5347_;
goto v___jp_5323_;
}
v___jp_5348_:
{
size_t v_sz_5358_; lean_object* v___x_5359_; 
v_sz_5358_ = lean_array_size(v___y_5357_);
v___x_5359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8(v_sortInfo_5227_, v___y_5357_, v_sz_5358_, v___y_5355_, v___y_5349_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
lean_dec_ref(v___y_5357_);
if (lean_obj_tag(v___x_5359_) == 0)
{
size_t v_sz_5360_; lean_object* v___x_5361_; 
lean_dec_ref_known(v___x_5359_, 1);
v_sz_5360_ = lean_array_size(v_groundFacts_5229_);
v___x_5361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9(v_groundFacts_5229_, v_sz_5360_, v___y_5355_, v___y_5349_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
if (lean_obj_tag(v___x_5361_) == 0)
{
size_t v_sz_5362_; lean_object* v___x_5363_; 
lean_dec_ref_known(v___x_5361_, 1);
v_sz_5362_ = lean_array_size(v_quantifiedFacts_5230_);
v___x_5363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10(v_quantifiedFacts_5230_, v_sz_5362_, v___y_5355_, v___y_5349_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
if (lean_obj_tag(v___x_5363_) == 0)
{
lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5370_; 
v_isSharedCheck_5370_ = !lean_is_exclusive(v___x_5363_);
if (v_isSharedCheck_5370_ == 0)
{
lean_object* v_unused_5371_; 
v_unused_5371_ = lean_ctor_get(v___x_5363_, 0);
lean_dec(v_unused_5371_);
v___x_5365_ = v___x_5363_;
v_isShared_5366_ = v_isSharedCheck_5370_;
goto v_resetjp_5364_;
}
else
{
lean_dec(v___x_5363_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5370_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v___x_5368_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set_tag(v___x_5365_, 1);
lean_ctor_set(v___x_5365_, 0, v___y_5349_);
v___x_5368_ = v___x_5365_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v___y_5349_);
v___x_5368_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
v___y_5324_ = v___y_5351_;
v___y_5325_ = v___y_5350_;
v___y_5326_ = v___y_5352_;
v___y_5327_ = v___y_5354_;
v___y_5328_ = v___y_5353_;
v___y_5329_ = v___y_5356_;
v_a_5330_ = v___x_5368_;
goto v___jp_5323_;
}
}
}
else
{
lean_object* v_a_5372_; 
v_a_5372_ = lean_ctor_get(v___x_5363_, 0);
lean_inc(v_a_5372_);
lean_dec_ref_known(v___x_5363_, 1);
v___y_5340_ = v___y_5350_;
v___y_5341_ = v___y_5351_;
v___y_5342_ = v___y_5352_;
v___y_5343_ = v___y_5353_;
v___y_5344_ = v___y_5354_;
v___y_5345_ = v___y_5356_;
v_a_5346_ = v_a_5372_;
goto v___jp_5339_;
}
}
else
{
lean_object* v_a_5373_; 
v_a_5373_ = lean_ctor_get(v___x_5361_, 0);
lean_inc(v_a_5373_);
lean_dec_ref_known(v___x_5361_, 1);
v___y_5340_ = v___y_5350_;
v___y_5341_ = v___y_5351_;
v___y_5342_ = v___y_5352_;
v___y_5343_ = v___y_5353_;
v___y_5344_ = v___y_5354_;
v___y_5345_ = v___y_5356_;
v_a_5346_ = v_a_5373_;
goto v___jp_5339_;
}
}
else
{
lean_object* v_a_5374_; 
v_a_5374_ = lean_ctor_get(v___x_5359_, 0);
lean_inc(v_a_5374_);
lean_dec_ref_known(v___x_5359_, 1);
v___y_5340_ = v___y_5350_;
v___y_5341_ = v___y_5351_;
v___y_5342_ = v___y_5352_;
v___y_5343_ = v___y_5353_;
v___y_5344_ = v___y_5354_;
v___y_5345_ = v___y_5356_;
v_a_5346_ = v_a_5374_;
goto v___jp_5339_;
}
}
v___jp_5375_:
{
lean_object* v___x_5388_; 
v___x_5388_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v___y_5382_, v___y_5386_, v___y_5384_, v___y_5387_);
lean_dec(v___y_5387_);
lean_dec(v___y_5382_);
v___y_5349_ = v___y_5376_;
v___y_5350_ = v___y_5378_;
v___y_5351_ = v___y_5377_;
v___y_5352_ = v___y_5379_;
v___y_5353_ = v___y_5381_;
v___y_5354_ = v___y_5380_;
v___y_5355_ = v___y_5383_;
v___y_5356_ = v___y_5385_;
v___y_5357_ = v___x_5388_;
goto v___jp_5348_;
}
v___jp_5389_:
{
uint8_t v___x_5402_; 
v___x_5402_ = lean_nat_dec_le(v___y_5401_, v___y_5398_);
if (v___x_5402_ == 0)
{
lean_dec(v___y_5398_);
lean_inc(v___y_5401_);
v___y_5376_ = v___y_5390_;
v___y_5377_ = v___y_5392_;
v___y_5378_ = v___y_5391_;
v___y_5379_ = v___y_5393_;
v___y_5380_ = v___y_5395_;
v___y_5381_ = v___y_5394_;
v___y_5382_ = v___y_5396_;
v___y_5383_ = v___y_5397_;
v___y_5384_ = v___y_5401_;
v___y_5385_ = v___y_5400_;
v___y_5386_ = v___y_5399_;
v___y_5387_ = v___y_5401_;
goto v___jp_5375_;
}
else
{
v___y_5376_ = v___y_5390_;
v___y_5377_ = v___y_5392_;
v___y_5378_ = v___y_5391_;
v___y_5379_ = v___y_5393_;
v___y_5380_ = v___y_5395_;
v___y_5381_ = v___y_5394_;
v___y_5382_ = v___y_5396_;
v___y_5383_ = v___y_5397_;
v___y_5384_ = v___y_5401_;
v___y_5385_ = v___y_5400_;
v___y_5386_ = v___y_5399_;
v___y_5387_ = v___y_5398_;
goto v___jp_5375_;
}
}
v___jp_5403_:
{
lean_object* v___x_5415_; uint8_t v___x_5416_; 
v___x_5415_ = lean_array_get_size(v___y_5414_);
v___x_5416_ = lean_nat_dec_eq(v___x_5415_, v___y_5408_);
if (v___x_5416_ == 0)
{
lean_object* v___x_5417_; uint8_t v___x_5418_; 
v___x_5417_ = lean_nat_sub(v___x_5415_, v___y_5411_);
v___x_5418_ = lean_nat_dec_le(v___y_5408_, v___x_5417_);
if (v___x_5418_ == 0)
{
lean_dec(v___y_5408_);
lean_inc(v___x_5417_);
v___y_5390_ = v___y_5404_;
v___y_5391_ = v___y_5406_;
v___y_5392_ = v___y_5405_;
v___y_5393_ = v___y_5407_;
v___y_5394_ = v___y_5410_;
v___y_5395_ = v___y_5409_;
v___y_5396_ = v___x_5415_;
v___y_5397_ = v___y_5412_;
v___y_5398_ = v___x_5417_;
v___y_5399_ = v___y_5414_;
v___y_5400_ = v___y_5413_;
v___y_5401_ = v___x_5417_;
goto v___jp_5389_;
}
else
{
v___y_5390_ = v___y_5404_;
v___y_5391_ = v___y_5406_;
v___y_5392_ = v___y_5405_;
v___y_5393_ = v___y_5407_;
v___y_5394_ = v___y_5410_;
v___y_5395_ = v___y_5409_;
v___y_5396_ = v___x_5415_;
v___y_5397_ = v___y_5412_;
v___y_5398_ = v___x_5417_;
v___y_5399_ = v___y_5414_;
v___y_5400_ = v___y_5413_;
v___y_5401_ = v___y_5408_;
goto v___jp_5389_;
}
}
else
{
lean_dec(v___y_5408_);
v___y_5349_ = v___y_5404_;
v___y_5350_ = v___y_5406_;
v___y_5351_ = v___y_5405_;
v___y_5352_ = v___y_5407_;
v___y_5353_ = v___y_5410_;
v___y_5354_ = v___y_5409_;
v___y_5355_ = v___y_5412_;
v___y_5356_ = v___y_5413_;
v___y_5357_ = v___y_5414_;
goto v___jp_5348_;
}
}
v___jp_5419_:
{
lean_object* v___x_5427_; double v___x_5428_; double v___x_5429_; double v___x_5430_; double v___x_5431_; double v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; 
v___x_5427_ = lean_io_mono_nanos_now();
v___x_5428_ = lean_float_of_nat(v___y_5425_);
v___x_5429_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___closed__1);
v___x_5430_ = lean_float_div(v___x_5428_, v___x_5429_);
v___x_5431_ = lean_float_of_nat(v___x_5427_);
v___x_5432_ = lean_float_div(v___x_5431_, v___x_5429_);
v___x_5433_ = lean_box_float(v___x_5430_);
v___x_5434_ = lean_box_float(v___x_5432_);
v___x_5435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5435_, 0, v___x_5433_);
lean_ctor_set(v___x_5435_, 1, v___x_5434_);
v___x_5436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5436_, 0, v_a_5426_);
lean_ctor_set(v___x_5436_, 1, v___x_5435_);
lean_inc_ref(v___y_5424_);
v___x_5437_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16(v_cls_5322_, v___y_5422_, v___y_5424_, v___y_5421_, v___y_5420_, v___y_5423_, v___f_5321_, v___x_5436_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
return v___x_5437_;
}
v___jp_5438_:
{
lean_object* v___x_5446_; 
v___x_5446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5446_, 0, v_a_5445_);
v___y_5420_ = v___y_5440_;
v___y_5421_ = v___y_5439_;
v___y_5422_ = v___y_5441_;
v___y_5423_ = v___y_5443_;
v___y_5424_ = v___y_5442_;
v___y_5425_ = v___y_5444_;
v_a_5426_ = v___x_5446_;
goto v___jp_5419_;
}
v___jp_5447_:
{
size_t v_sz_5457_; lean_object* v___x_5458_; 
v_sz_5457_ = lean_array_size(v___y_5456_);
v___x_5458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__8(v_sortInfo_5227_, v___y_5456_, v_sz_5457_, v___y_5454_, v___y_5448_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
lean_dec_ref(v___y_5456_);
if (lean_obj_tag(v___x_5458_) == 0)
{
size_t v_sz_5459_; lean_object* v___x_5460_; 
lean_dec_ref_known(v___x_5458_, 1);
v_sz_5459_ = lean_array_size(v_groundFacts_5229_);
v___x_5460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__9(v_groundFacts_5229_, v_sz_5459_, v___y_5454_, v___y_5448_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
if (lean_obj_tag(v___x_5460_) == 0)
{
size_t v_sz_5461_; lean_object* v___x_5462_; 
lean_dec_ref_known(v___x_5460_, 1);
v_sz_5461_ = lean_array_size(v_quantifiedFacts_5230_);
v___x_5462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__10(v_quantifiedFacts_5230_, v_sz_5461_, v___y_5454_, v___y_5448_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
if (lean_obj_tag(v___x_5462_) == 0)
{
lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5469_; 
v_isSharedCheck_5469_ = !lean_is_exclusive(v___x_5462_);
if (v_isSharedCheck_5469_ == 0)
{
lean_object* v_unused_5470_; 
v_unused_5470_ = lean_ctor_get(v___x_5462_, 0);
lean_dec(v_unused_5470_);
v___x_5464_ = v___x_5462_;
v_isShared_5465_ = v_isSharedCheck_5469_;
goto v_resetjp_5463_;
}
else
{
lean_dec(v___x_5462_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5469_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5467_; 
if (v_isShared_5465_ == 0)
{
lean_ctor_set_tag(v___x_5464_, 1);
lean_ctor_set(v___x_5464_, 0, v___y_5448_);
v___x_5467_ = v___x_5464_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5468_; 
v_reuseFailAlloc_5468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5468_, 0, v___y_5448_);
v___x_5467_ = v_reuseFailAlloc_5468_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
v___y_5420_ = v___y_5450_;
v___y_5421_ = v___y_5449_;
v___y_5422_ = v___y_5451_;
v___y_5423_ = v___y_5453_;
v___y_5424_ = v___y_5452_;
v___y_5425_ = v___y_5455_;
v_a_5426_ = v___x_5467_;
goto v___jp_5419_;
}
}
}
else
{
lean_object* v_a_5471_; 
v_a_5471_ = lean_ctor_get(v___x_5462_, 0);
lean_inc(v_a_5471_);
lean_dec_ref_known(v___x_5462_, 1);
v___y_5439_ = v___y_5449_;
v___y_5440_ = v___y_5450_;
v___y_5441_ = v___y_5451_;
v___y_5442_ = v___y_5452_;
v___y_5443_ = v___y_5453_;
v___y_5444_ = v___y_5455_;
v_a_5445_ = v_a_5471_;
goto v___jp_5438_;
}
}
else
{
lean_object* v_a_5472_; 
v_a_5472_ = lean_ctor_get(v___x_5460_, 0);
lean_inc(v_a_5472_);
lean_dec_ref_known(v___x_5460_, 1);
v___y_5439_ = v___y_5449_;
v___y_5440_ = v___y_5450_;
v___y_5441_ = v___y_5451_;
v___y_5442_ = v___y_5452_;
v___y_5443_ = v___y_5453_;
v___y_5444_ = v___y_5455_;
v_a_5445_ = v_a_5472_;
goto v___jp_5438_;
}
}
else
{
lean_object* v_a_5473_; 
v_a_5473_ = lean_ctor_get(v___x_5458_, 0);
lean_inc(v_a_5473_);
lean_dec_ref_known(v___x_5458_, 1);
v___y_5439_ = v___y_5449_;
v___y_5440_ = v___y_5450_;
v___y_5441_ = v___y_5451_;
v___y_5442_ = v___y_5452_;
v___y_5443_ = v___y_5453_;
v___y_5444_ = v___y_5455_;
v_a_5445_ = v_a_5473_;
goto v___jp_5438_;
}
}
v___jp_5474_:
{
lean_object* v___x_5487_; 
v___x_5487_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v___y_5479_, v___y_5482_, v___y_5485_, v___y_5486_);
lean_dec(v___y_5486_);
lean_dec(v___y_5479_);
v___y_5448_ = v___y_5475_;
v___y_5449_ = v___y_5477_;
v___y_5450_ = v___y_5476_;
v___y_5451_ = v___y_5478_;
v___y_5452_ = v___y_5481_;
v___y_5453_ = v___y_5480_;
v___y_5454_ = v___y_5483_;
v___y_5455_ = v___y_5484_;
v___y_5456_ = v___x_5487_;
goto v___jp_5447_;
}
v___jp_5488_:
{
uint8_t v___x_5501_; 
v___x_5501_ = lean_nat_dec_le(v___y_5500_, v___y_5499_);
if (v___x_5501_ == 0)
{
lean_dec(v___y_5499_);
lean_inc(v___y_5500_);
v___y_5475_ = v___y_5489_;
v___y_5476_ = v___y_5491_;
v___y_5477_ = v___y_5490_;
v___y_5478_ = v___y_5493_;
v___y_5479_ = v___y_5492_;
v___y_5480_ = v___y_5495_;
v___y_5481_ = v___y_5494_;
v___y_5482_ = v___y_5496_;
v___y_5483_ = v___y_5497_;
v___y_5484_ = v___y_5498_;
v___y_5485_ = v___y_5500_;
v___y_5486_ = v___y_5500_;
goto v___jp_5474_;
}
else
{
v___y_5475_ = v___y_5489_;
v___y_5476_ = v___y_5491_;
v___y_5477_ = v___y_5490_;
v___y_5478_ = v___y_5493_;
v___y_5479_ = v___y_5492_;
v___y_5480_ = v___y_5495_;
v___y_5481_ = v___y_5494_;
v___y_5482_ = v___y_5496_;
v___y_5483_ = v___y_5497_;
v___y_5484_ = v___y_5498_;
v___y_5485_ = v___y_5500_;
v___y_5486_ = v___y_5499_;
goto v___jp_5474_;
}
}
v___jp_5502_:
{
lean_object* v___x_5514_; uint8_t v___x_5515_; 
v___x_5514_ = lean_array_get_size(v___y_5513_);
v___x_5515_ = lean_nat_dec_eq(v___x_5514_, v___y_5507_);
if (v___x_5515_ == 0)
{
lean_object* v___x_5516_; uint8_t v___x_5517_; 
v___x_5516_ = lean_nat_sub(v___x_5514_, v___y_5510_);
v___x_5517_ = lean_nat_dec_le(v___y_5507_, v___x_5516_);
if (v___x_5517_ == 0)
{
lean_dec(v___y_5507_);
lean_inc(v___x_5516_);
v___y_5489_ = v___y_5503_;
v___y_5490_ = v___y_5505_;
v___y_5491_ = v___y_5504_;
v___y_5492_ = v___x_5514_;
v___y_5493_ = v___y_5506_;
v___y_5494_ = v___y_5509_;
v___y_5495_ = v___y_5508_;
v___y_5496_ = v___y_5513_;
v___y_5497_ = v___y_5511_;
v___y_5498_ = v___y_5512_;
v___y_5499_ = v___x_5516_;
v___y_5500_ = v___x_5516_;
goto v___jp_5488_;
}
else
{
v___y_5489_ = v___y_5503_;
v___y_5490_ = v___y_5505_;
v___y_5491_ = v___y_5504_;
v___y_5492_ = v___x_5514_;
v___y_5493_ = v___y_5506_;
v___y_5494_ = v___y_5509_;
v___y_5495_ = v___y_5508_;
v___y_5496_ = v___y_5513_;
v___y_5497_ = v___y_5511_;
v___y_5498_ = v___y_5512_;
v___y_5499_ = v___x_5516_;
v___y_5500_ = v___y_5507_;
goto v___jp_5488_;
}
}
else
{
lean_dec(v___y_5507_);
v___y_5448_ = v___y_5503_;
v___y_5449_ = v___y_5505_;
v___y_5450_ = v___y_5504_;
v___y_5451_ = v___y_5506_;
v___y_5452_ = v___y_5509_;
v___y_5453_ = v___y_5508_;
v___y_5454_ = v___y_5511_;
v___y_5455_ = v___y_5512_;
v___y_5456_ = v___y_5513_;
goto v___jp_5447_;
}
}
v___jp_5518_:
{
lean_object* v___x_5529_; lean_object* v_a_5530_; lean_object* v___x_5531_; uint8_t v___x_5532_; 
v___x_5529_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__14___redArg(v_a_5225_);
v_a_5530_ = lean_ctor_get(v___x_5529_, 0);
lean_inc(v_a_5530_);
lean_dec_ref(v___x_5529_);
v___x_5531_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5532_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15(v___y_5522_, v___x_5531_);
if (v___x_5532_ == 0)
{
lean_object* v___x_5533_; lean_object* v___x_5534_; 
v___x_5533_ = lean_io_mono_nanos_now();
v___x_5534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7(v___y_5526_, v___y_5519_, v___y_5528_, v___y_5520_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
lean_dec_ref(v___y_5526_);
if (lean_obj_tag(v___x_5534_) == 0)
{
lean_object* v_size_5535_; lean_object* v_buckets_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; uint8_t v___x_5539_; 
lean_dec_ref_known(v___x_5534_, 1);
v_size_5535_ = lean_ctor_get(v_predInfo_5228_, 0);
v_buckets_5536_ = lean_ctor_get(v_predInfo_5228_, 1);
v___x_5537_ = lean_mk_empty_array_with_capacity(v_size_5535_);
v___x_5538_ = lean_array_get_size(v_buckets_5536_);
v___x_5539_ = lean_nat_dec_lt(v___y_5524_, v___x_5538_);
if (v___x_5539_ == 0)
{
v___y_5503_ = v___y_5520_;
v___y_5504_ = v___y_5521_;
v___y_5505_ = v___y_5522_;
v___y_5506_ = v___y_5523_;
v___y_5507_ = v___y_5524_;
v___y_5508_ = v_a_5530_;
v___y_5509_ = v___y_5525_;
v___y_5510_ = v___y_5527_;
v___y_5511_ = v___y_5528_;
v___y_5512_ = v___x_5533_;
v___y_5513_ = v___x_5537_;
goto v___jp_5502_;
}
else
{
size_t v___x_5540_; lean_object* v___x_5541_; 
v___x_5540_ = lean_usize_of_nat(v___x_5538_);
v___x_5541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13(v_buckets_5536_, v___y_5528_, v___x_5540_, v___x_5537_);
v___y_5503_ = v___y_5520_;
v___y_5504_ = v___y_5521_;
v___y_5505_ = v___y_5522_;
v___y_5506_ = v___y_5523_;
v___y_5507_ = v___y_5524_;
v___y_5508_ = v_a_5530_;
v___y_5509_ = v___y_5525_;
v___y_5510_ = v___y_5527_;
v___y_5511_ = v___y_5528_;
v___y_5512_ = v___x_5533_;
v___y_5513_ = v___x_5541_;
goto v___jp_5502_;
}
}
else
{
lean_object* v_a_5542_; 
lean_dec(v___y_5524_);
v_a_5542_ = lean_ctor_get(v___x_5534_, 0);
lean_inc(v_a_5542_);
lean_dec_ref_known(v___x_5534_, 1);
v___y_5439_ = v___y_5522_;
v___y_5440_ = v___y_5521_;
v___y_5441_ = v___y_5523_;
v___y_5442_ = v___y_5525_;
v___y_5443_ = v_a_5530_;
v___y_5444_ = v___x_5533_;
v_a_5445_ = v_a_5542_;
goto v___jp_5438_;
}
}
else
{
lean_object* v___x_5543_; lean_object* v___x_5544_; 
v___x_5543_ = lean_io_get_num_heartbeats();
v___x_5544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7(v___y_5526_, v___y_5519_, v___y_5528_, v___y_5520_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
lean_dec_ref(v___y_5526_);
if (lean_obj_tag(v___x_5544_) == 0)
{
lean_object* v_size_5545_; lean_object* v_buckets_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; uint8_t v___x_5549_; 
lean_dec_ref_known(v___x_5544_, 1);
v_size_5545_ = lean_ctor_get(v_predInfo_5228_, 0);
v_buckets_5546_ = lean_ctor_get(v_predInfo_5228_, 1);
v___x_5547_ = lean_mk_empty_array_with_capacity(v_size_5545_);
v___x_5548_ = lean_array_get_size(v_buckets_5546_);
v___x_5549_ = lean_nat_dec_lt(v___y_5524_, v___x_5548_);
if (v___x_5549_ == 0)
{
v___y_5404_ = v___y_5520_;
v___y_5405_ = v___y_5521_;
v___y_5406_ = v___y_5522_;
v___y_5407_ = v___y_5523_;
v___y_5408_ = v___y_5524_;
v___y_5409_ = v_a_5530_;
v___y_5410_ = v___y_5525_;
v___y_5411_ = v___y_5527_;
v___y_5412_ = v___y_5528_;
v___y_5413_ = v___x_5543_;
v___y_5414_ = v___x_5547_;
goto v___jp_5403_;
}
else
{
size_t v___x_5550_; lean_object* v___x_5551_; 
v___x_5550_ = lean_usize_of_nat(v___x_5548_);
v___x_5551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13(v_buckets_5546_, v___y_5528_, v___x_5550_, v___x_5547_);
v___y_5404_ = v___y_5520_;
v___y_5405_ = v___y_5521_;
v___y_5406_ = v___y_5522_;
v___y_5407_ = v___y_5523_;
v___y_5408_ = v___y_5524_;
v___y_5409_ = v_a_5530_;
v___y_5410_ = v___y_5525_;
v___y_5411_ = v___y_5527_;
v___y_5412_ = v___y_5528_;
v___y_5413_ = v___x_5543_;
v___y_5414_ = v___x_5551_;
goto v___jp_5403_;
}
}
else
{
lean_object* v_a_5552_; 
lean_dec(v___y_5524_);
v_a_5552_ = lean_ctor_get(v___x_5544_, 0);
lean_inc(v_a_5552_);
lean_dec_ref_known(v___x_5544_, 1);
v___y_5340_ = v___y_5522_;
v___y_5341_ = v___y_5521_;
v___y_5342_ = v___y_5523_;
v___y_5343_ = v___y_5525_;
v___y_5344_ = v_a_5530_;
v___y_5345_ = v___x_5543_;
v_a_5346_ = v_a_5552_;
goto v___jp_5339_;
}
}
}
v___jp_5553_:
{
lean_object* v_toCold_5557_; lean_object* v_options_5558_; lean_object* v_inheritedTraceOptions_5559_; uint8_t v_hasTrace_5560_; lean_object* v___x_5561_; size_t v_sz_5562_; size_t v___x_5563_; 
v_toCold_5557_ = lean_ctor_get(v_a_5224_, 0);
v_options_5558_ = lean_ctor_get(v_toCold_5557_, 2);
v_inheritedTraceOptions_5559_ = lean_ctor_get(v_toCold_5557_, 11);
v_hasTrace_5560_ = lean_ctor_get_uint8(v_options_5558_, sizeof(void*)*1);
v___x_5561_ = lean_box(0);
v_sz_5562_ = lean_array_size(v___y_5556_);
v___x_5563_ = ((size_t)0ULL);
if (v_hasTrace_5560_ == 0)
{
lean_object* v___x_5564_; 
v___x_5564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7(v___y_5556_, v_sz_5562_, v___x_5563_, v___x_5561_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
lean_dec_ref(v___y_5556_);
if (lean_obj_tag(v___x_5564_) == 0)
{
lean_object* v_size_5565_; lean_object* v_buckets_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; uint8_t v___x_5569_; 
lean_dec_ref_known(v___x_5564_, 1);
v_size_5565_ = lean_ctor_get(v_predInfo_5228_, 0);
v_buckets_5566_ = lean_ctor_get(v_predInfo_5228_, 1);
v___x_5567_ = lean_mk_empty_array_with_capacity(v_size_5565_);
v___x_5568_ = lean_array_get_size(v_buckets_5566_);
v___x_5569_ = lean_nat_dec_lt(v___y_5554_, v___x_5568_);
if (v___x_5569_ == 0)
{
v___y_5266_ = v___x_5561_;
v___y_5267_ = v___y_5554_;
v___y_5268_ = v___y_5555_;
v___y_5269_ = v___x_5563_;
v___y_5270_ = v___x_5567_;
goto v___jp_5265_;
}
else
{
size_t v___x_5570_; lean_object* v___x_5571_; 
v___x_5570_ = lean_usize_of_nat(v___x_5568_);
v___x_5571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13(v_buckets_5566_, v___x_5563_, v___x_5570_, v___x_5567_);
v___y_5266_ = v___x_5561_;
v___y_5267_ = v___y_5554_;
v___y_5268_ = v___y_5555_;
v___y_5269_ = v___x_5563_;
v___y_5270_ = v___x_5571_;
goto v___jp_5265_;
}
}
else
{
lean_dec(v___y_5554_);
return v___x_5564_;
}
}
else
{
lean_object* v___x_5572_; lean_object* v___x_5573_; uint8_t v___x_5574_; 
v___x_5572_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__1));
v___x_5573_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__9);
v___x_5574_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5559_, v_options_5558_, v___x_5573_);
if (v___x_5574_ == 0)
{
lean_object* v___x_5575_; uint8_t v___x_5576_; 
v___x_5575_ = l_Lean_trace_profiler;
v___x_5576_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__15(v_options_5558_, v___x_5575_);
if (v___x_5576_ == 0)
{
lean_object* v___x_5577_; 
v___x_5577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__7(v___y_5556_, v_sz_5562_, v___x_5563_, v___x_5561_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
lean_dec_ref(v___y_5556_);
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v_size_5578_; lean_object* v_buckets_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; uint8_t v___x_5582_; 
lean_dec_ref_known(v___x_5577_, 1);
v_size_5578_ = lean_ctor_get(v_predInfo_5228_, 0);
v_buckets_5579_ = lean_ctor_get(v_predInfo_5228_, 1);
v___x_5580_ = lean_mk_empty_array_with_capacity(v_size_5578_);
v___x_5581_ = lean_array_get_size(v_buckets_5579_);
v___x_5582_ = lean_nat_dec_lt(v___y_5554_, v___x_5581_);
if (v___x_5582_ == 0)
{
v___y_5310_ = v___x_5561_;
v___y_5311_ = v___y_5554_;
v___y_5312_ = v___y_5555_;
v___y_5313_ = v___x_5563_;
v___y_5314_ = v___x_5580_;
goto v___jp_5309_;
}
else
{
size_t v___x_5583_; lean_object* v___x_5584_; 
v___x_5583_ = lean_usize_of_nat(v___x_5581_);
v___x_5584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__13(v_buckets_5579_, v___x_5563_, v___x_5583_, v___x_5580_);
v___y_5310_ = v___x_5561_;
v___y_5311_ = v___y_5554_;
v___y_5312_ = v___y_5555_;
v___y_5313_ = v___x_5563_;
v___y_5314_ = v___x_5584_;
goto v___jp_5309_;
}
}
else
{
lean_dec(v___y_5554_);
return v___x_5577_;
}
}
else
{
v___y_5519_ = v_sz_5562_;
v___y_5520_ = v___x_5561_;
v___y_5521_ = v___x_5574_;
v___y_5522_ = v_options_5558_;
v___y_5523_ = v_hasTrace_5560_;
v___y_5524_ = v___y_5554_;
v___y_5525_ = v___x_5572_;
v___y_5526_ = v___y_5556_;
v___y_5527_ = v___y_5555_;
v___y_5528_ = v___x_5563_;
goto v___jp_5518_;
}
}
else
{
v___y_5519_ = v_sz_5562_;
v___y_5520_ = v___x_5561_;
v___y_5521_ = v___x_5574_;
v___y_5522_ = v_options_5558_;
v___y_5523_ = v_hasTrace_5560_;
v___y_5524_ = v___y_5554_;
v___y_5525_ = v___x_5572_;
v___y_5526_ = v___y_5556_;
v___y_5527_ = v___y_5555_;
v___y_5528_ = v___x_5563_;
goto v___jp_5518_;
}
}
}
v___jp_5585_:
{
lean_object* v___x_5592_; 
v___x_5592_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg(v___y_5586_, v___y_5589_, v___y_5590_, v___y_5591_);
lean_dec(v___y_5591_);
lean_dec(v___y_5586_);
v___y_5554_ = v___y_5587_;
v___y_5555_ = v___y_5588_;
v___y_5556_ = v___x_5592_;
goto v___jp_5553_;
}
v___jp_5593_:
{
uint8_t v___x_5600_; 
v___x_5600_ = lean_nat_dec_le(v___y_5599_, v___y_5595_);
if (v___x_5600_ == 0)
{
lean_dec(v___y_5595_);
lean_inc(v___y_5599_);
v___y_5586_ = v___y_5594_;
v___y_5587_ = v___y_5596_;
v___y_5588_ = v___y_5597_;
v___y_5589_ = v___y_5598_;
v___y_5590_ = v___y_5599_;
v___y_5591_ = v___y_5599_;
goto v___jp_5585_;
}
else
{
v___y_5586_ = v___y_5594_;
v___y_5587_ = v___y_5596_;
v___y_5588_ = v___y_5597_;
v___y_5589_ = v___y_5598_;
v___y_5590_ = v___y_5599_;
v___y_5591_ = v___y_5595_;
goto v___jp_5585_;
}
}
v___jp_5601_:
{
lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; uint8_t v___x_5606_; 
v___x_5603_ = lean_unsigned_to_nat(0u);
v___x_5604_ = lean_unsigned_to_nat(1u);
v___x_5605_ = lean_array_get_size(v___y_5602_);
v___x_5606_ = lean_nat_dec_eq(v___x_5605_, v___x_5603_);
if (v___x_5606_ == 0)
{
lean_object* v___x_5607_; uint8_t v___x_5608_; 
v___x_5607_ = lean_nat_sub(v___x_5605_, v___x_5604_);
v___x_5608_ = lean_nat_dec_le(v___x_5603_, v___x_5607_);
if (v___x_5608_ == 0)
{
lean_inc(v___x_5607_);
v___y_5594_ = v___x_5605_;
v___y_5595_ = v___x_5607_;
v___y_5596_ = v___x_5603_;
v___y_5597_ = v___x_5604_;
v___y_5598_ = v___y_5602_;
v___y_5599_ = v___x_5607_;
goto v___jp_5593_;
}
else
{
v___y_5594_ = v___x_5605_;
v___y_5595_ = v___x_5607_;
v___y_5596_ = v___x_5603_;
v___y_5597_ = v___x_5604_;
v___y_5598_ = v___y_5602_;
v___y_5599_ = v___x_5603_;
goto v___jp_5593_;
}
}
else
{
v___y_5554_ = v___x_5603_;
v___y_5555_ = v___x_5604_;
v___y_5556_ = v___y_5602_;
goto v___jp_5553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem___boxed(lean_object* v_problem_5616_, lean_object* v_a_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_){
_start:
{
lean_object* v_res_5622_; 
v_res_5622_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem(v_problem_5616_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_);
lean_dec(v_a_5620_);
lean_dec_ref(v_a_5619_);
lean_dec(v_a_5618_);
lean_dec_ref(v_a_5617_);
lean_dec_ref(v_problem_5616_);
return v_res_5622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11(lean_object* v_n_5623_, lean_object* v_as_5624_, lean_object* v_lo_5625_, lean_object* v_hi_5626_, lean_object* v_w_5627_, lean_object* v_hlo_5628_, lean_object* v_hhi_5629_){
_start:
{
lean_object* v___x_5630_; 
v___x_5630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___redArg(v_n_5623_, v_as_5624_, v_lo_5625_, v_hi_5626_);
return v___x_5630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11___boxed(lean_object* v_n_5631_, lean_object* v_as_5632_, lean_object* v_lo_5633_, lean_object* v_hi_5634_, lean_object* v_w_5635_, lean_object* v_hlo_5636_, lean_object* v_hhi_5637_){
_start:
{
lean_object* v_res_5638_; 
v_res_5638_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11(v_n_5631_, v_as_5632_, v_lo_5633_, v_hi_5634_, v_w_5635_, v_hlo_5636_, v_hhi_5637_);
lean_dec(v_hi_5634_);
lean_dec(v_n_5631_);
return v_res_5638_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19(lean_object* v_00_u03b1_5639_, lean_object* v_x_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_){
_start:
{
lean_object* v___x_5646_; 
v___x_5646_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___redArg(v_x_5640_);
return v___x_5646_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19___boxed(lean_object* v_00_u03b1_5647_, lean_object* v_x_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_){
_start:
{
lean_object* v_res_5654_; 
v_res_5654_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__16_spec__19(v_00_u03b1_5647_, v_x_5648_, v___y_5649_, v___y_5650_, v___y_5651_, v___y_5652_);
lean_dec(v___y_5652_);
lean_dec_ref(v___y_5651_);
lean_dec(v___y_5650_);
lean_dec_ref(v___y_5649_);
return v_res_5654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17(lean_object* v_n_5655_, lean_object* v_as_5656_, lean_object* v_lo_5657_, lean_object* v_hi_5658_, lean_object* v_w_5659_, lean_object* v_hlo_5660_, lean_object* v_hhi_5661_){
_start:
{
lean_object* v___x_5662_; 
v___x_5662_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___redArg(v_n_5655_, v_as_5656_, v_lo_5657_, v_hi_5658_);
return v___x_5662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17___boxed(lean_object* v_n_5663_, lean_object* v_as_5664_, lean_object* v_lo_5665_, lean_object* v_hi_5666_, lean_object* v_w_5667_, lean_object* v_hlo_5668_, lean_object* v_hhi_5669_){
_start:
{
lean_object* v_res_5670_; 
v_res_5670_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17(v_n_5663_, v_as_5664_, v_lo_5665_, v_hi_5666_, v_w_5667_, v_hlo_5668_, v_hhi_5669_);
lean_dec(v_hi_5666_);
lean_dec(v_n_5663_);
return v_res_5670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12(lean_object* v_n_5671_, lean_object* v_lo_5672_, lean_object* v_hi_5673_, lean_object* v_hhi_5674_, lean_object* v_pivot_5675_, lean_object* v_as_5676_, lean_object* v_i_5677_, lean_object* v_k_5678_, lean_object* v_ilo_5679_, lean_object* v_ik_5680_, lean_object* v_w_5681_){
_start:
{
lean_object* v___x_5682_; 
v___x_5682_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___redArg(v_hi_5673_, v_pivot_5675_, v_as_5676_, v_i_5677_, v_k_5678_);
return v___x_5682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12___boxed(lean_object* v_n_5683_, lean_object* v_lo_5684_, lean_object* v_hi_5685_, lean_object* v_hhi_5686_, lean_object* v_pivot_5687_, lean_object* v_as_5688_, lean_object* v_i_5689_, lean_object* v_k_5690_, lean_object* v_ilo_5691_, lean_object* v_ik_5692_, lean_object* v_w_5693_){
_start:
{
lean_object* v_res_5694_; 
v_res_5694_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__11_spec__12(v_n_5683_, v_lo_5684_, v_hi_5685_, v_hhi_5686_, v_pivot_5687_, v_as_5688_, v_i_5689_, v_k_5690_, v_ilo_5691_, v_ik_5692_, v_w_5693_);
lean_dec_ref(v_pivot_5687_);
lean_dec(v_hi_5685_);
lean_dec(v_lo_5684_);
lean_dec(v_n_5683_);
return v_res_5694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23(lean_object* v_n_5695_, lean_object* v_lo_5696_, lean_object* v_hi_5697_, lean_object* v_hhi_5698_, lean_object* v_pivot_5699_, lean_object* v_as_5700_, lean_object* v_i_5701_, lean_object* v_k_5702_, lean_object* v_ilo_5703_, lean_object* v_ik_5704_, lean_object* v_w_5705_){
_start:
{
lean_object* v___x_5706_; 
v___x_5706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___redArg(v_hi_5697_, v_pivot_5699_, v_as_5700_, v_i_5701_, v_k_5702_);
return v___x_5706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23___boxed(lean_object* v_n_5707_, lean_object* v_lo_5708_, lean_object* v_hi_5709_, lean_object* v_hhi_5710_, lean_object* v_pivot_5711_, lean_object* v_as_5712_, lean_object* v_i_5713_, lean_object* v_k_5714_, lean_object* v_ilo_5715_, lean_object* v_ik_5716_, lean_object* v_w_5717_){
_start:
{
lean_object* v_res_5718_; 
v_res_5718_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem_spec__17_spec__23(v_n_5707_, v_lo_5708_, v_hi_5709_, v_hhi_5710_, v_pivot_5711_, v_as_5712_, v_i_5713_, v_k_5714_, v_ilo_5715_, v_ik_5716_, v_w_5717_);
lean_dec_ref(v_pivot_5711_);
lean_dec(v_hi_5709_);
lean_dec(v_lo_5708_);
lean_dec(v_n_5707_);
return v_res_5718_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg___lam__0(lean_object* v_x_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_){
_start:
{
lean_object* v___x_5727_; 
lean_inc(v___y_5721_);
lean_inc_ref(v___y_5720_);
v___x_5727_ = lean_apply_7(v_x_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, lean_box(0));
return v___x_5727_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg___lam__0___boxed(lean_object* v_x_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_){
_start:
{
lean_object* v_res_5736_; 
v_res_5736_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg___lam__0(v_x_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_);
lean_dec(v___y_5730_);
lean_dec_ref(v___y_5729_);
return v_res_5736_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg(lean_object* v_mvarId_5737_, lean_object* v_x_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_){
_start:
{
lean_object* v___f_5746_; lean_object* v___x_5747_; 
lean_inc(v___y_5740_);
lean_inc_ref(v___y_5739_);
v___f_5746_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_5746_, 0, v_x_5738_);
lean_closure_set(v___f_5746_, 1, v___y_5739_);
lean_closure_set(v___f_5746_, 2, v___y_5740_);
v___x_5747_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_5737_, v___f_5746_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_);
if (lean_obj_tag(v___x_5747_) == 0)
{
return v___x_5747_;
}
else
{
lean_object* v_a_5748_; lean_object* v___x_5750_; uint8_t v_isShared_5751_; uint8_t v_isSharedCheck_5755_; 
v_a_5748_ = lean_ctor_get(v___x_5747_, 0);
v_isSharedCheck_5755_ = !lean_is_exclusive(v___x_5747_);
if (v_isSharedCheck_5755_ == 0)
{
v___x_5750_ = v___x_5747_;
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
else
{
lean_inc(v_a_5748_);
lean_dec(v___x_5747_);
v___x_5750_ = lean_box(0);
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
v_resetjp_5749_:
{
lean_object* v___x_5753_; 
if (v_isShared_5751_ == 0)
{
v___x_5753_ = v___x_5750_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_a_5748_);
v___x_5753_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
return v___x_5753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg___boxed(lean_object* v_mvarId_5756_, lean_object* v_x_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_){
_start:
{
lean_object* v_res_5765_; 
v_res_5765_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg(v_mvarId_5756_, v_x_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_);
lean_dec(v___y_5763_);
lean_dec_ref(v___y_5762_);
lean_dec(v___y_5761_);
lean_dec_ref(v___y_5760_);
lean_dec(v___y_5759_);
lean_dec_ref(v___y_5758_);
return v_res_5765_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0(lean_object* v_00_u03b1_5766_, lean_object* v_mvarId_5767_, lean_object* v_x_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_){
_start:
{
lean_object* v___x_5776_; 
v___x_5776_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg(v_mvarId_5767_, v_x_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_, v___y_5774_);
return v___x_5776_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___boxed(lean_object* v_00_u03b1_5777_, lean_object* v_mvarId_5778_, lean_object* v_x_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_){
_start:
{
lean_object* v_res_5787_; 
v_res_5787_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0(v_00_u03b1_5777_, v_mvarId_5778_, v_x_5779_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_);
lean_dec(v___y_5785_);
lean_dec_ref(v___y_5784_);
lean_dec(v___y_5783_);
lean_dec_ref(v___y_5782_);
lean_dec(v___y_5781_);
lean_dec_ref(v___y_5780_);
return v_res_5787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode___lam__0(lean_object* v_hyps_5788_, lean_object* v_g_5789_, uint8_t v_symBreak_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_){
_start:
{
lean_object* v___x_5798_; 
v___x_5798_ = l_Lean_Meta_Tactic_BVDecide_EPR_detectEprProblem(v_hyps_5788_, v___y_5791_, v___y_5792_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_);
if (lean_obj_tag(v___x_5798_) == 0)
{
lean_object* v_a_5799_; lean_object* v___x_5801_; uint8_t v_isShared_5802_; uint8_t v_isSharedCheck_5861_; 
v_a_5799_ = lean_ctor_get(v___x_5798_, 0);
v_isSharedCheck_5861_ = !lean_is_exclusive(v___x_5798_);
if (v_isSharedCheck_5861_ == 0)
{
v___x_5801_ = v___x_5798_;
v_isShared_5802_ = v_isSharedCheck_5861_;
goto v_resetjp_5800_;
}
else
{
lean_inc(v_a_5799_);
lean_dec(v___x_5798_);
v___x_5801_ = lean_box(0);
v_isShared_5802_ = v_isSharedCheck_5861_;
goto v_resetjp_5800_;
}
v_resetjp_5800_:
{
lean_object* v_problem_5803_; lean_object* v_remainingHyps_5804_; lean_object* v___x_5806_; uint8_t v_isShared_5807_; uint8_t v_isSharedCheck_5860_; 
v_problem_5803_ = lean_ctor_get(v_a_5799_, 0);
v_remainingHyps_5804_ = lean_ctor_get(v_a_5799_, 1);
v_isSharedCheck_5860_ = !lean_is_exclusive(v_a_5799_);
if (v_isSharedCheck_5860_ == 0)
{
v___x_5806_ = v_a_5799_;
v_isShared_5807_ = v_isSharedCheck_5860_;
goto v_resetjp_5805_;
}
else
{
lean_inc(v_remainingHyps_5804_);
lean_inc(v_problem_5803_);
lean_dec(v_a_5799_);
v___x_5806_ = lean_box(0);
v_isShared_5807_ = v_isSharedCheck_5860_;
goto v_resetjp_5805_;
}
v_resetjp_5805_:
{
lean_object* v_groundFacts_5849_; lean_object* v_quantifiedFacts_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; uint8_t v___x_5853_; 
v_groundFacts_5849_ = lean_ctor_get(v_problem_5803_, 3);
v_quantifiedFacts_5850_ = lean_ctor_get(v_problem_5803_, 4);
v___x_5851_ = lean_array_get_size(v_groundFacts_5849_);
v___x_5852_ = lean_unsigned_to_nat(0u);
v___x_5853_ = lean_nat_dec_eq(v___x_5851_, v___x_5852_);
if (v___x_5853_ == 0)
{
lean_del_object(v___x_5801_);
goto v___jp_5808_;
}
else
{
lean_object* v___x_5854_; uint8_t v___x_5855_; 
v___x_5854_ = lean_array_get_size(v_quantifiedFacts_5850_);
v___x_5855_ = lean_nat_dec_eq(v___x_5854_, v___x_5852_);
if (v___x_5855_ == 0)
{
lean_del_object(v___x_5801_);
goto v___jp_5808_;
}
else
{
lean_object* v___x_5856_; lean_object* v___x_5858_; 
lean_del_object(v___x_5806_);
lean_dec_ref(v_remainingHyps_5804_);
lean_dec_ref(v_problem_5803_);
lean_dec(v_g_5789_);
v___x_5856_ = lean_box(0);
if (v_isShared_5802_ == 0)
{
lean_ctor_set(v___x_5801_, 0, v___x_5856_);
v___x_5858_ = v___x_5801_;
goto v_reusejp_5857_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v___x_5856_);
v___x_5858_ = v_reuseFailAlloc_5859_;
goto v_reusejp_5857_;
}
v_reusejp_5857_:
{
return v___x_5858_;
}
}
}
v___jp_5808_:
{
lean_object* v___x_5809_; 
v___x_5809_ = l_Lean_Meta_Tactic_BVDecide_EPR_EprProblem_inferSorts(v_problem_5803_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_);
if (lean_obj_tag(v___x_5809_) == 0)
{
lean_object* v_a_5810_; lean_object* v___x_5811_; 
v_a_5810_ = lean_ctor_get(v___x_5809_, 0);
lean_inc(v_a_5810_);
lean_dec_ref_known(v___x_5809_, 1);
v___x_5811_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_traceProblem(v_a_5810_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_);
if (lean_obj_tag(v___x_5811_) == 0)
{
lean_object* v___x_5812_; 
lean_dec_ref_known(v___x_5811_, 1);
v___x_5812_ = l_Lean_Meta_Tactic_BVDecide_EPR_epr2BitVec(v_a_5810_, v_g_5789_, v_symBreak_5790_, v___y_5791_, v___y_5792_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_);
if (lean_obj_tag(v___x_5812_) == 0)
{
lean_object* v_a_5813_; lean_object* v___x_5815_; uint8_t v_isShared_5816_; uint8_t v_isSharedCheck_5824_; 
v_a_5813_ = lean_ctor_get(v___x_5812_, 0);
v_isSharedCheck_5824_ = !lean_is_exclusive(v___x_5812_);
if (v_isSharedCheck_5824_ == 0)
{
v___x_5815_ = v___x_5812_;
v_isShared_5816_ = v_isSharedCheck_5824_;
goto v_resetjp_5814_;
}
else
{
lean_inc(v_a_5813_);
lean_dec(v___x_5812_);
v___x_5815_ = lean_box(0);
v_isShared_5816_ = v_isSharedCheck_5824_;
goto v_resetjp_5814_;
}
v_resetjp_5814_:
{
lean_object* v___x_5818_; 
if (v_isShared_5807_ == 0)
{
lean_ctor_set(v___x_5806_, 1, v_a_5813_);
lean_ctor_set(v___x_5806_, 0, v_remainingHyps_5804_);
v___x_5818_ = v___x_5806_;
goto v_reusejp_5817_;
}
else
{
lean_object* v_reuseFailAlloc_5823_; 
v_reuseFailAlloc_5823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5823_, 0, v_remainingHyps_5804_);
lean_ctor_set(v_reuseFailAlloc_5823_, 1, v_a_5813_);
v___x_5818_ = v_reuseFailAlloc_5823_;
goto v_reusejp_5817_;
}
v_reusejp_5817_:
{
lean_object* v___x_5819_; lean_object* v___x_5821_; 
v___x_5819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5819_, 0, v___x_5818_);
if (v_isShared_5816_ == 0)
{
lean_ctor_set(v___x_5815_, 0, v___x_5819_);
v___x_5821_ = v___x_5815_;
goto v_reusejp_5820_;
}
else
{
lean_object* v_reuseFailAlloc_5822_; 
v_reuseFailAlloc_5822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5822_, 0, v___x_5819_);
v___x_5821_ = v_reuseFailAlloc_5822_;
goto v_reusejp_5820_;
}
v_reusejp_5820_:
{
return v___x_5821_;
}
}
}
}
else
{
lean_object* v_a_5825_; lean_object* v___x_5827_; uint8_t v_isShared_5828_; uint8_t v_isSharedCheck_5832_; 
lean_del_object(v___x_5806_);
lean_dec_ref(v_remainingHyps_5804_);
v_a_5825_ = lean_ctor_get(v___x_5812_, 0);
v_isSharedCheck_5832_ = !lean_is_exclusive(v___x_5812_);
if (v_isSharedCheck_5832_ == 0)
{
v___x_5827_ = v___x_5812_;
v_isShared_5828_ = v_isSharedCheck_5832_;
goto v_resetjp_5826_;
}
else
{
lean_inc(v_a_5825_);
lean_dec(v___x_5812_);
v___x_5827_ = lean_box(0);
v_isShared_5828_ = v_isSharedCheck_5832_;
goto v_resetjp_5826_;
}
v_resetjp_5826_:
{
lean_object* v___x_5830_; 
if (v_isShared_5828_ == 0)
{
v___x_5830_ = v___x_5827_;
goto v_reusejp_5829_;
}
else
{
lean_object* v_reuseFailAlloc_5831_; 
v_reuseFailAlloc_5831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5831_, 0, v_a_5825_);
v___x_5830_ = v_reuseFailAlloc_5831_;
goto v_reusejp_5829_;
}
v_reusejp_5829_:
{
return v___x_5830_;
}
}
}
}
else
{
lean_object* v_a_5833_; lean_object* v___x_5835_; uint8_t v_isShared_5836_; uint8_t v_isSharedCheck_5840_; 
lean_dec(v_a_5810_);
lean_del_object(v___x_5806_);
lean_dec_ref(v_remainingHyps_5804_);
lean_dec(v_g_5789_);
v_a_5833_ = lean_ctor_get(v___x_5811_, 0);
v_isSharedCheck_5840_ = !lean_is_exclusive(v___x_5811_);
if (v_isSharedCheck_5840_ == 0)
{
v___x_5835_ = v___x_5811_;
v_isShared_5836_ = v_isSharedCheck_5840_;
goto v_resetjp_5834_;
}
else
{
lean_inc(v_a_5833_);
lean_dec(v___x_5811_);
v___x_5835_ = lean_box(0);
v_isShared_5836_ = v_isSharedCheck_5840_;
goto v_resetjp_5834_;
}
v_resetjp_5834_:
{
lean_object* v___x_5838_; 
if (v_isShared_5836_ == 0)
{
v___x_5838_ = v___x_5835_;
goto v_reusejp_5837_;
}
else
{
lean_object* v_reuseFailAlloc_5839_; 
v_reuseFailAlloc_5839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5839_, 0, v_a_5833_);
v___x_5838_ = v_reuseFailAlloc_5839_;
goto v_reusejp_5837_;
}
v_reusejp_5837_:
{
return v___x_5838_;
}
}
}
}
else
{
lean_object* v_a_5841_; lean_object* v___x_5843_; uint8_t v_isShared_5844_; uint8_t v_isSharedCheck_5848_; 
lean_del_object(v___x_5806_);
lean_dec_ref(v_remainingHyps_5804_);
lean_dec(v_g_5789_);
v_a_5841_ = lean_ctor_get(v___x_5809_, 0);
v_isSharedCheck_5848_ = !lean_is_exclusive(v___x_5809_);
if (v_isSharedCheck_5848_ == 0)
{
v___x_5843_ = v___x_5809_;
v_isShared_5844_ = v_isSharedCheck_5848_;
goto v_resetjp_5842_;
}
else
{
lean_inc(v_a_5841_);
lean_dec(v___x_5809_);
v___x_5843_ = lean_box(0);
v_isShared_5844_ = v_isSharedCheck_5848_;
goto v_resetjp_5842_;
}
v_resetjp_5842_:
{
lean_object* v___x_5846_; 
if (v_isShared_5844_ == 0)
{
v___x_5846_ = v___x_5843_;
goto v_reusejp_5845_;
}
else
{
lean_object* v_reuseFailAlloc_5847_; 
v_reuseFailAlloc_5847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5847_, 0, v_a_5841_);
v___x_5846_ = v_reuseFailAlloc_5847_;
goto v_reusejp_5845_;
}
v_reusejp_5845_:
{
return v___x_5846_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5869_; 
lean_dec(v_g_5789_);
v_a_5862_ = lean_ctor_get(v___x_5798_, 0);
v_isSharedCheck_5869_ = !lean_is_exclusive(v___x_5798_);
if (v_isSharedCheck_5869_ == 0)
{
v___x_5864_ = v___x_5798_;
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_a_5862_);
lean_dec(v___x_5798_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v___x_5867_; 
if (v_isShared_5865_ == 0)
{
v___x_5867_ = v___x_5864_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v_a_5862_);
v___x_5867_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
return v___x_5867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode___lam__0___boxed(lean_object* v_hyps_5870_, lean_object* v_g_5871_, lean_object* v_symBreak_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_){
_start:
{
uint8_t v_symBreak_boxed_5880_; lean_object* v_res_5881_; 
v_symBreak_boxed_5880_ = lean_unbox(v_symBreak_5872_);
v_res_5881_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode___lam__0(v_hyps_5870_, v_g_5871_, v_symBreak_boxed_5880_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_);
lean_dec(v___y_5878_);
lean_dec_ref(v___y_5877_);
lean_dec(v___y_5876_);
lean_dec_ref(v___y_5875_);
lean_dec(v___y_5874_);
lean_dec_ref(v___y_5873_);
lean_dec_ref(v_hyps_5870_);
return v_res_5881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode(lean_object* v_g_5882_, lean_object* v_hyps_5883_, uint8_t v_symBreak_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_, lean_object* v_a_5887_, lean_object* v_a_5888_, lean_object* v_a_5889_, lean_object* v_a_5890_){
_start:
{
lean_object* v___x_5892_; lean_object* v___f_5893_; lean_object* v___x_5894_; 
v___x_5892_ = lean_box(v_symBreak_5884_);
lean_inc(v_g_5882_);
v___f_5893_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5893_, 0, v_hyps_5883_);
lean_closure_set(v___f_5893_, 1, v_g_5882_);
lean_closure_set(v___f_5893_, 2, v___x_5892_);
v___x_5894_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode_spec__0___redArg(v_g_5882_, v___f_5893_, v_a_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_);
return v___x_5894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode___boxed(lean_object* v_g_5895_, lean_object* v_hyps_5896_, lean_object* v_symBreak_5897_, lean_object* v_a_5898_, lean_object* v_a_5899_, lean_object* v_a_5900_, lean_object* v_a_5901_, lean_object* v_a_5902_, lean_object* v_a_5903_, lean_object* v_a_5904_){
_start:
{
uint8_t v_symBreak_boxed_5905_; lean_object* v_res_5906_; 
v_symBreak_boxed_5905_ = lean_unbox(v_symBreak_5897_);
v_res_5906_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode(v_g_5895_, v_hyps_5896_, v_symBreak_boxed_5905_, v_a_5898_, v_a_5899_, v_a_5900_, v_a_5901_, v_a_5902_, v_a_5903_);
lean_dec(v_a_5903_);
lean_dec_ref(v_a_5902_);
lean_dec(v_a_5901_);
lean_dec_ref(v_a_5900_);
lean_dec(v_a_5899_);
lean_dec_ref(v_a_5898_);
return v_res_5906_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___redArg(lean_object* v_cls_5907_, lean_object* v_msg_5908_, lean_object* v___y_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_){
_start:
{
lean_object* v_ref_5914_; lean_object* v___x_5915_; lean_object* v_a_5916_; lean_object* v___x_5918_; uint8_t v_isShared_5919_; uint8_t v_isSharedCheck_5961_; 
v_ref_5914_ = lean_ctor_get(v___y_5911_, 2);
v___x_5915_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5_spec__8(v_msg_5908_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_);
v_a_5916_ = lean_ctor_get(v___x_5915_, 0);
v_isSharedCheck_5961_ = !lean_is_exclusive(v___x_5915_);
if (v_isSharedCheck_5961_ == 0)
{
v___x_5918_ = v___x_5915_;
v_isShared_5919_ = v_isSharedCheck_5961_;
goto v_resetjp_5917_;
}
else
{
lean_inc(v_a_5916_);
lean_dec(v___x_5915_);
v___x_5918_ = lean_box(0);
v_isShared_5919_ = v_isSharedCheck_5961_;
goto v_resetjp_5917_;
}
v_resetjp_5917_:
{
lean_object* v___x_5920_; lean_object* v_traceState_5921_; lean_object* v_env_5922_; lean_object* v_nextMacroScope_5923_; lean_object* v_ngen_5924_; lean_object* v_auxDeclNGen_5925_; lean_object* v_cache_5926_; lean_object* v_recordedDeps_5927_; lean_object* v_messages_5928_; lean_object* v_infoState_5929_; lean_object* v_snapshotTasks_5930_; lean_object* v___x_5932_; uint8_t v_isShared_5933_; uint8_t v_isSharedCheck_5960_; 
v___x_5920_ = lean_st_ref_take(v___y_5912_);
v_traceState_5921_ = lean_ctor_get(v___x_5920_, 4);
v_env_5922_ = lean_ctor_get(v___x_5920_, 0);
v_nextMacroScope_5923_ = lean_ctor_get(v___x_5920_, 1);
v_ngen_5924_ = lean_ctor_get(v___x_5920_, 2);
v_auxDeclNGen_5925_ = lean_ctor_get(v___x_5920_, 3);
v_cache_5926_ = lean_ctor_get(v___x_5920_, 5);
v_recordedDeps_5927_ = lean_ctor_get(v___x_5920_, 6);
v_messages_5928_ = lean_ctor_get(v___x_5920_, 7);
v_infoState_5929_ = lean_ctor_get(v___x_5920_, 8);
v_snapshotTasks_5930_ = lean_ctor_get(v___x_5920_, 9);
v_isSharedCheck_5960_ = !lean_is_exclusive(v___x_5920_);
if (v_isSharedCheck_5960_ == 0)
{
v___x_5932_ = v___x_5920_;
v_isShared_5933_ = v_isSharedCheck_5960_;
goto v_resetjp_5931_;
}
else
{
lean_inc(v_snapshotTasks_5930_);
lean_inc(v_infoState_5929_);
lean_inc(v_messages_5928_);
lean_inc(v_recordedDeps_5927_);
lean_inc(v_cache_5926_);
lean_inc(v_traceState_5921_);
lean_inc(v_auxDeclNGen_5925_);
lean_inc(v_ngen_5924_);
lean_inc(v_nextMacroScope_5923_);
lean_inc(v_env_5922_);
lean_dec(v___x_5920_);
v___x_5932_ = lean_box(0);
v_isShared_5933_ = v_isSharedCheck_5960_;
goto v_resetjp_5931_;
}
v_resetjp_5931_:
{
uint64_t v_tid_5934_; lean_object* v_traces_5935_; lean_object* v___x_5937_; uint8_t v_isShared_5938_; uint8_t v_isSharedCheck_5959_; 
v_tid_5934_ = lean_ctor_get_uint64(v_traceState_5921_, sizeof(void*)*1);
v_traces_5935_ = lean_ctor_get(v_traceState_5921_, 0);
v_isSharedCheck_5959_ = !lean_is_exclusive(v_traceState_5921_);
if (v_isSharedCheck_5959_ == 0)
{
v___x_5937_ = v_traceState_5921_;
v_isShared_5938_ = v_isSharedCheck_5959_;
goto v_resetjp_5936_;
}
else
{
lean_inc(v_traces_5935_);
lean_dec(v_traceState_5921_);
v___x_5937_ = lean_box(0);
v_isShared_5938_ = v_isSharedCheck_5959_;
goto v_resetjp_5936_;
}
v_resetjp_5936_:
{
lean_object* v___x_5939_; lean_object* v___x_5940_; double v___x_5941_; uint8_t v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5950_; 
v___x_5939_ = lean_box(0);
v___x_5940_ = lean_box(0);
v___x_5941_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__0);
v___x_5942_ = 0;
v___x_5943_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__1));
v___x_5944_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5944_, 0, v_cls_5907_);
lean_ctor_set(v___x_5944_, 1, v___x_5940_);
lean_ctor_set(v___x_5944_, 2, v___x_5943_);
lean_ctor_set_float(v___x_5944_, sizeof(void*)*3, v___x_5941_);
lean_ctor_set_float(v___x_5944_, sizeof(void*)*3 + 8, v___x_5941_);
lean_ctor_set_uint8(v___x_5944_, sizeof(void*)*3 + 16, v___x_5942_);
v___x_5945_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f_spec__5___redArg___closed__2));
v___x_5946_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5944_);
lean_ctor_set(v___x_5946_, 1, v_a_5916_);
lean_ctor_set(v___x_5946_, 2, v___x_5945_);
lean_inc(v_ref_5914_);
v___x_5947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5947_, 0, v_ref_5914_);
lean_ctor_set(v___x_5947_, 1, v___x_5946_);
v___x_5948_ = l_Lean_PersistentArray_push___redArg(v_traces_5935_, v___x_5947_);
if (v_isShared_5938_ == 0)
{
lean_ctor_set(v___x_5937_, 0, v___x_5948_);
v___x_5950_ = v___x_5937_;
goto v_reusejp_5949_;
}
else
{
lean_object* v_reuseFailAlloc_5958_; 
v_reuseFailAlloc_5958_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5958_, 0, v___x_5948_);
lean_ctor_set_uint64(v_reuseFailAlloc_5958_, sizeof(void*)*1, v_tid_5934_);
v___x_5950_ = v_reuseFailAlloc_5958_;
goto v_reusejp_5949_;
}
v_reusejp_5949_:
{
lean_object* v___x_5952_; 
if (v_isShared_5933_ == 0)
{
lean_ctor_set(v___x_5932_, 4, v___x_5950_);
v___x_5952_ = v___x_5932_;
goto v_reusejp_5951_;
}
else
{
lean_object* v_reuseFailAlloc_5957_; 
v_reuseFailAlloc_5957_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5957_, 0, v_env_5922_);
lean_ctor_set(v_reuseFailAlloc_5957_, 1, v_nextMacroScope_5923_);
lean_ctor_set(v_reuseFailAlloc_5957_, 2, v_ngen_5924_);
lean_ctor_set(v_reuseFailAlloc_5957_, 3, v_auxDeclNGen_5925_);
lean_ctor_set(v_reuseFailAlloc_5957_, 4, v___x_5950_);
lean_ctor_set(v_reuseFailAlloc_5957_, 5, v_cache_5926_);
lean_ctor_set(v_reuseFailAlloc_5957_, 6, v_recordedDeps_5927_);
lean_ctor_set(v_reuseFailAlloc_5957_, 7, v_messages_5928_);
lean_ctor_set(v_reuseFailAlloc_5957_, 8, v_infoState_5929_);
lean_ctor_set(v_reuseFailAlloc_5957_, 9, v_snapshotTasks_5930_);
v___x_5952_ = v_reuseFailAlloc_5957_;
goto v_reusejp_5951_;
}
v_reusejp_5951_:
{
lean_object* v___x_5953_; lean_object* v___x_5955_; 
v___x_5953_ = lean_st_ref_put(v___y_5912_, v___x_5952_);
if (v_isShared_5919_ == 0)
{
lean_ctor_set(v___x_5918_, 0, v___x_5939_);
v___x_5955_ = v___x_5918_;
goto v_reusejp_5954_;
}
else
{
lean_object* v_reuseFailAlloc_5956_; 
v_reuseFailAlloc_5956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5956_, 0, v___x_5939_);
v___x_5955_ = v_reuseFailAlloc_5956_;
goto v_reusejp_5954_;
}
v_reusejp_5954_:
{
return v___x_5955_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___redArg___boxed(lean_object* v_cls_5962_, lean_object* v_msg_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_){
_start:
{
lean_object* v_res_5969_; 
v_res_5969_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___redArg(v_cls_5962_, v_msg_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_);
lean_dec(v___y_5967_);
lean_dec_ref(v___y_5966_);
lean_dec(v___y_5965_);
lean_dec_ref(v___y_5964_);
return v_res_5969_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__1(void){
_start:
{
lean_object* v_cls_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; 
v_cls_5974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__0));
v___x_5975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_DetectM_checkFact_x3f___closed__8));
v___x_5976_ = l_Lean_Name_append(v___x_5975_, v_cls_5974_);
return v___x_5976_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__3(void){
_start:
{
lean_object* v___x_5978_; lean_object* v___x_5979_; 
v___x_5978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__2));
v___x_5979_ = l_Lean_stringToMessageData(v___x_5978_);
return v___x_5979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1(lean_object* v_as_5980_, size_t v_i_5981_, size_t v_stop_5982_, lean_object* v_b_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_){
_start:
{
lean_object* v_a_5997_; uint8_t v___x_6003_; 
v___x_6003_ = lean_usize_dec_eq(v_i_5981_, v_stop_5982_);
if (v___x_6003_ == 0)
{
lean_object* v_toCold_6004_; lean_object* v_options_6005_; uint8_t v_hasTrace_6006_; 
v_toCold_6004_ = lean_ctor_get(v___y_5993_, 0);
v_options_6005_ = lean_ctor_get(v_toCold_6004_, 2);
v_hasTrace_6006_ = lean_ctor_get_uint8(v_options_6005_, sizeof(void*)*1);
if (v_hasTrace_6006_ == 0)
{
goto v___jp_6001_;
}
else
{
lean_object* v_inheritedTraceOptions_6007_; lean_object* v_cls_6008_; lean_object* v___x_6009_; uint8_t v___x_6010_; 
v_inheritedTraceOptions_6007_ = lean_ctor_get(v_toCold_6004_, 11);
v_cls_6008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__0));
v___x_6009_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__1);
v___x_6010_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6007_, v_options_6005_, v___x_6009_);
if (v___x_6010_ == 0)
{
goto v___jp_6001_;
}
else
{
lean_object* v___x_6011_; lean_object* v_type_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; 
v___x_6011_ = lean_array_uget_borrowed(v_as_5980_, v_i_5981_);
v_type_6012_ = lean_ctor_get(v___x_6011_, 1);
v___x_6013_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___closed__3);
lean_inc_ref(v_type_6012_);
v___x_6014_ = l_Lean_MessageData_ofExpr(v_type_6012_);
v___x_6015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6013_);
lean_ctor_set(v___x_6015_, 1, v___x_6014_);
v___x_6016_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___redArg(v_cls_6008_, v___x_6015_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_);
if (lean_obj_tag(v___x_6016_) == 0)
{
lean_object* v_a_6017_; 
v_a_6017_ = lean_ctor_get(v___x_6016_, 0);
lean_inc(v_a_6017_);
lean_dec_ref_known(v___x_6016_, 1);
v_a_5997_ = v_a_6017_;
goto v___jp_5996_;
}
else
{
return v___x_6016_;
}
}
}
}
else
{
lean_object* v___x_6018_; 
v___x_6018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6018_, 0, v_b_5983_);
return v___x_6018_;
}
v___jp_5996_:
{
size_t v___x_5998_; size_t v___x_5999_; 
v___x_5998_ = ((size_t)1ULL);
v___x_5999_ = lean_usize_add(v_i_5981_, v___x_5998_);
v_i_5981_ = v___x_5999_;
v_b_5983_ = v_a_5997_;
goto _start;
}
v___jp_6001_:
{
lean_object* v___x_6002_; 
v___x_6002_ = lean_box(0);
v_a_5997_ = v___x_6002_;
goto v___jp_5996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1___boxed(lean_object* v_as_6019_, lean_object* v_i_6020_, lean_object* v_stop_6021_, lean_object* v_b_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v___y_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_){
_start:
{
size_t v_i_boxed_6035_; size_t v_stop_boxed_6036_; lean_object* v_res_6037_; 
v_i_boxed_6035_ = lean_unbox_usize(v_i_6020_);
lean_dec(v_i_6020_);
v_stop_boxed_6036_ = lean_unbox_usize(v_stop_6021_);
lean_dec(v_stop_6021_);
v_res_6037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1(v_as_6019_, v_i_boxed_6035_, v_stop_boxed_6036_, v_b_6022_, v___y_6023_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_);
lean_dec(v___y_6033_);
lean_dec_ref(v___y_6032_);
lean_dec(v___y_6031_);
lean_dec_ref(v___y_6030_);
lean_dec(v___y_6029_);
lean_dec_ref(v___y_6028_);
lean_dec(v___y_6027_);
lean_dec_ref(v___y_6026_);
lean_dec(v___y_6025_);
lean_dec(v___y_6024_);
lean_dec_ref(v___y_6023_);
lean_dec_ref(v_as_6019_);
return v_res_6037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___lam__0(lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_){
_start:
{
lean_object* v___x_6050_; lean_object* v_config_6051_; lean_object* v_target_6052_; uint8_t v_eprSymBreak_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v_hypotheses_6056_; lean_object* v___x_6057_; 
v___x_6050_ = lean_st_ref_get(v___y_6039_);
v_config_6051_ = lean_ctor_get(v___y_6038_, 0);
v_target_6052_ = lean_ctor_get(v___x_6050_, 2);
lean_inc_ref(v_target_6052_);
lean_dec(v___x_6050_);
v_eprSymBreak_6053_ = lean_ctor_get_uint8(v_config_6051_, sizeof(void*)*3 + 13);
v___x_6054_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_6052_);
lean_dec_ref(v_target_6052_);
v___x_6055_ = lean_st_ref_get(v___y_6039_);
v_hypotheses_6056_ = lean_ctor_get(v___x_6055_, 3);
lean_inc_ref(v_hypotheses_6056_);
lean_dec(v___x_6055_);
v___x_6057_ = l___private_Lean_Meta_Tactic_BVDecide_EPR_Pass_0__Lean_Meta_Tactic_BVDecide_EPR_detectAndEncode(v___x_6054_, v_hypotheses_6056_, v_eprSymBreak_6053_, v___y_6043_, v___y_6044_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_);
if (lean_obj_tag(v___x_6057_) == 0)
{
lean_object* v_a_6058_; lean_object* v___x_6060_; uint8_t v_isShared_6061_; uint8_t v_isSharedCheck_6123_; 
v_a_6058_ = lean_ctor_get(v___x_6057_, 0);
v_isSharedCheck_6123_ = !lean_is_exclusive(v___x_6057_);
if (v_isSharedCheck_6123_ == 0)
{
v___x_6060_ = v___x_6057_;
v_isShared_6061_ = v_isSharedCheck_6123_;
goto v_resetjp_6059_;
}
else
{
lean_inc(v_a_6058_);
lean_dec(v___x_6057_);
v___x_6060_ = lean_box(0);
v_isShared_6061_ = v_isSharedCheck_6123_;
goto v_resetjp_6059_;
}
v_resetjp_6059_:
{
if (lean_obj_tag(v_a_6058_) == 1)
{
lean_object* v_val_6062_; lean_object* v_fst_6063_; lean_object* v_snd_6064_; lean_object* v___x_6065_; lean_object* v_caches_6066_; lean_object* v_typeAnalysis_6067_; lean_object* v_target_6068_; uint8_t v_didChange_6069_; lean_object* v___x_6071_; uint8_t v_isShared_6072_; uint8_t v_isSharedCheck_6115_; 
v_val_6062_ = lean_ctor_get(v_a_6058_, 0);
lean_inc(v_val_6062_);
lean_dec_ref_known(v_a_6058_, 1);
v_fst_6063_ = lean_ctor_get(v_val_6062_, 0);
lean_inc(v_fst_6063_);
v_snd_6064_ = lean_ctor_get(v_val_6062_, 1);
lean_inc(v_snd_6064_);
lean_dec(v_val_6062_);
v___x_6065_ = lean_st_ref_take(v___y_6039_);
v_caches_6066_ = lean_ctor_get(v___x_6065_, 0);
v_typeAnalysis_6067_ = lean_ctor_get(v___x_6065_, 1);
v_target_6068_ = lean_ctor_get(v___x_6065_, 2);
v_didChange_6069_ = lean_ctor_get_uint8(v___x_6065_, sizeof(void*)*5);
v_isSharedCheck_6115_ = !lean_is_exclusive(v___x_6065_);
if (v_isSharedCheck_6115_ == 0)
{
lean_object* v_unused_6116_; lean_object* v_unused_6117_; 
v_unused_6116_ = lean_ctor_get(v___x_6065_, 4);
lean_dec(v_unused_6116_);
v_unused_6117_ = lean_ctor_get(v___x_6065_, 3);
lean_dec(v_unused_6117_);
v___x_6071_ = v___x_6065_;
v_isShared_6072_ = v_isSharedCheck_6115_;
goto v_resetjp_6070_;
}
else
{
lean_inc(v_target_6068_);
lean_inc(v_typeAnalysis_6067_);
lean_inc(v_caches_6066_);
lean_dec(v___x_6065_);
v___x_6071_ = lean_box(0);
v_isShared_6072_ = v_isSharedCheck_6115_;
goto v_resetjp_6070_;
}
v_resetjp_6070_:
{
lean_object* v___x_6074_; 
lean_inc(v_snd_6064_);
if (v_isShared_6072_ == 0)
{
lean_ctor_set(v___x_6071_, 4, v_snd_6064_);
lean_ctor_set(v___x_6071_, 3, v_fst_6063_);
v___x_6074_ = v___x_6071_;
goto v_reusejp_6073_;
}
else
{
lean_object* v_reuseFailAlloc_6114_; 
v_reuseFailAlloc_6114_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_6114_, 0, v_caches_6066_);
lean_ctor_set(v_reuseFailAlloc_6114_, 1, v_typeAnalysis_6067_);
lean_ctor_set(v_reuseFailAlloc_6114_, 2, v_target_6068_);
lean_ctor_set(v_reuseFailAlloc_6114_, 3, v_fst_6063_);
lean_ctor_set(v_reuseFailAlloc_6114_, 4, v_snd_6064_);
lean_ctor_set_uint8(v_reuseFailAlloc_6114_, sizeof(void*)*5, v_didChange_6069_);
v___x_6074_ = v_reuseFailAlloc_6114_;
goto v_reusejp_6073_;
}
v_reusejp_6073_:
{
lean_object* v___x_6075_; lean_object* v_groundFacts_6076_; lean_object* v___x_6099_; lean_object* v___x_6100_; uint8_t v___x_6101_; 
v___x_6075_ = lean_st_ref_put(v___y_6039_, v___x_6074_);
v_groundFacts_6076_ = lean_ctor_get(v_snd_6064_, 3);
lean_inc_ref(v_groundFacts_6076_);
lean_dec(v_snd_6064_);
v___x_6099_ = lean_unsigned_to_nat(0u);
v___x_6100_ = lean_array_get_size(v_groundFacts_6076_);
v___x_6101_ = lean_nat_dec_lt(v___x_6099_, v___x_6100_);
if (v___x_6101_ == 0)
{
goto v___jp_6077_;
}
else
{
lean_object* v___x_6102_; size_t v___x_6103_; size_t v___x_6104_; lean_object* v___x_6105_; 
v___x_6102_ = lean_box(0);
v___x_6103_ = ((size_t)0ULL);
v___x_6104_ = lean_usize_of_nat(v___x_6100_);
v___x_6105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__1(v_groundFacts_6076_, v___x_6103_, v___x_6104_, v___x_6102_, v___y_6038_, v___y_6039_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_, v___y_6044_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_);
if (lean_obj_tag(v___x_6105_) == 0)
{
lean_dec_ref_known(v___x_6105_, 1);
goto v___jp_6077_;
}
else
{
lean_object* v_a_6106_; lean_object* v___x_6108_; uint8_t v_isShared_6109_; uint8_t v_isSharedCheck_6113_; 
lean_dec_ref(v_groundFacts_6076_);
lean_del_object(v___x_6060_);
v_a_6106_ = lean_ctor_get(v___x_6105_, 0);
v_isSharedCheck_6113_ = !lean_is_exclusive(v___x_6105_);
if (v_isSharedCheck_6113_ == 0)
{
v___x_6108_ = v___x_6105_;
v_isShared_6109_ = v_isSharedCheck_6113_;
goto v_resetjp_6107_;
}
else
{
lean_inc(v_a_6106_);
lean_dec(v___x_6105_);
v___x_6108_ = lean_box(0);
v_isShared_6109_ = v_isSharedCheck_6113_;
goto v_resetjp_6107_;
}
v_resetjp_6107_:
{
lean_object* v___x_6111_; 
if (v_isShared_6109_ == 0)
{
v___x_6111_ = v___x_6108_;
goto v_reusejp_6110_;
}
else
{
lean_object* v_reuseFailAlloc_6112_; 
v_reuseFailAlloc_6112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6112_, 0, v_a_6106_);
v___x_6111_ = v_reuseFailAlloc_6112_;
goto v_reusejp_6110_;
}
v_reusejp_6110_:
{
return v___x_6111_;
}
}
}
}
v___jp_6077_:
{
lean_object* v___x_6078_; lean_object* v_caches_6079_; lean_object* v_typeAnalysis_6080_; lean_object* v_target_6081_; lean_object* v_hypotheses_6082_; uint8_t v_didChange_6083_; lean_object* v_eprBvProblem_6084_; lean_object* v___x_6086_; uint8_t v_isShared_6087_; uint8_t v_isSharedCheck_6098_; 
v___x_6078_ = lean_st_ref_take(v___y_6039_);
v_caches_6079_ = lean_ctor_get(v___x_6078_, 0);
v_typeAnalysis_6080_ = lean_ctor_get(v___x_6078_, 1);
v_target_6081_ = lean_ctor_get(v___x_6078_, 2);
v_hypotheses_6082_ = lean_ctor_get(v___x_6078_, 3);
v_didChange_6083_ = lean_ctor_get_uint8(v___x_6078_, sizeof(void*)*5);
v_eprBvProblem_6084_ = lean_ctor_get(v___x_6078_, 4);
v_isSharedCheck_6098_ = !lean_is_exclusive(v___x_6078_);
if (v_isSharedCheck_6098_ == 0)
{
v___x_6086_ = v___x_6078_;
v_isShared_6087_ = v_isSharedCheck_6098_;
goto v_resetjp_6085_;
}
else
{
lean_inc(v_eprBvProblem_6084_);
lean_inc(v_hypotheses_6082_);
lean_inc(v_target_6081_);
lean_inc(v_typeAnalysis_6080_);
lean_inc(v_caches_6079_);
lean_dec(v___x_6078_);
v___x_6086_ = lean_box(0);
v_isShared_6087_ = v_isSharedCheck_6098_;
goto v_resetjp_6085_;
}
v_resetjp_6085_:
{
lean_object* v___x_6088_; lean_object* v___x_6090_; 
v___x_6088_ = l_Array_append___redArg(v_hypotheses_6082_, v_groundFacts_6076_);
lean_dec_ref(v_groundFacts_6076_);
if (v_isShared_6087_ == 0)
{
lean_ctor_set(v___x_6086_, 3, v___x_6088_);
v___x_6090_ = v___x_6086_;
goto v_reusejp_6089_;
}
else
{
lean_object* v_reuseFailAlloc_6097_; 
v_reuseFailAlloc_6097_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_6097_, 0, v_caches_6079_);
lean_ctor_set(v_reuseFailAlloc_6097_, 1, v_typeAnalysis_6080_);
lean_ctor_set(v_reuseFailAlloc_6097_, 2, v_target_6081_);
lean_ctor_set(v_reuseFailAlloc_6097_, 3, v___x_6088_);
lean_ctor_set(v_reuseFailAlloc_6097_, 4, v_eprBvProblem_6084_);
lean_ctor_set_uint8(v_reuseFailAlloc_6097_, sizeof(void*)*5, v_didChange_6083_);
v___x_6090_ = v_reuseFailAlloc_6097_;
goto v_reusejp_6089_;
}
v_reusejp_6089_:
{
lean_object* v___x_6091_; uint8_t v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6095_; 
v___x_6091_ = lean_st_ref_put(v___y_6039_, v___x_6090_);
v___x_6092_ = 0;
v___x_6093_ = lean_box(v___x_6092_);
if (v_isShared_6061_ == 0)
{
lean_ctor_set(v___x_6060_, 0, v___x_6093_);
v___x_6095_ = v___x_6060_;
goto v_reusejp_6094_;
}
else
{
lean_object* v_reuseFailAlloc_6096_; 
v_reuseFailAlloc_6096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6096_, 0, v___x_6093_);
v___x_6095_ = v_reuseFailAlloc_6096_;
goto v_reusejp_6094_;
}
v_reusejp_6094_:
{
return v___x_6095_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6121_; 
lean_dec(v_a_6058_);
v___x_6118_ = 0;
v___x_6119_ = lean_box(v___x_6118_);
if (v_isShared_6061_ == 0)
{
lean_ctor_set(v___x_6060_, 0, v___x_6119_);
v___x_6121_ = v___x_6060_;
goto v_reusejp_6120_;
}
else
{
lean_object* v_reuseFailAlloc_6122_; 
v_reuseFailAlloc_6122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6122_, 0, v___x_6119_);
v___x_6121_ = v_reuseFailAlloc_6122_;
goto v_reusejp_6120_;
}
v_reusejp_6120_:
{
return v___x_6121_;
}
}
}
}
else
{
lean_object* v_a_6124_; lean_object* v___x_6126_; uint8_t v_isShared_6127_; uint8_t v_isSharedCheck_6131_; 
v_a_6124_ = lean_ctor_get(v___x_6057_, 0);
v_isSharedCheck_6131_ = !lean_is_exclusive(v___x_6057_);
if (v_isSharedCheck_6131_ == 0)
{
v___x_6126_ = v___x_6057_;
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
else
{
lean_inc(v_a_6124_);
lean_dec(v___x_6057_);
v___x_6126_ = lean_box(0);
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
v_resetjp_6125_:
{
lean_object* v___x_6129_; 
if (v_isShared_6127_ == 0)
{
v___x_6129_ = v___x_6126_;
goto v_reusejp_6128_;
}
else
{
lean_object* v_reuseFailAlloc_6130_; 
v_reuseFailAlloc_6130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6130_, 0, v_a_6124_);
v___x_6129_ = v_reuseFailAlloc_6130_;
goto v_reusejp_6128_;
}
v_reusejp_6128_:
{
return v___x_6129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___lam__0___boxed(lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_){
_start:
{
lean_object* v_res_6144_; 
v_res_6144_ = l_Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass___lam__0(v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_);
lean_dec(v___y_6142_);
lean_dec_ref(v___y_6141_);
lean_dec(v___y_6140_);
lean_dec_ref(v___y_6139_);
lean_dec(v___y_6138_);
lean_dec_ref(v___y_6137_);
lean_dec(v___y_6136_);
lean_dec_ref(v___y_6135_);
lean_dec(v___y_6134_);
lean_dec(v___y_6133_);
lean_dec_ref(v___y_6132_);
return v_res_6144_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0(lean_object* v_cls_6153_, lean_object* v_msg_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_){
_start:
{
lean_object* v___x_6167_; 
v___x_6167_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___redArg(v_cls_6153_, v_msg_6154_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_);
return v___x_6167_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0___boxed(lean_object* v_cls_6168_, lean_object* v_msg_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_){
_start:
{
lean_object* v_res_6182_; 
v_res_6182_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_EPR_eprDetectPass_spec__0(v_cls_6168_, v_msg_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_);
lean_dec(v___y_6180_);
lean_dec_ref(v___y_6179_);
lean_dec(v___y_6178_);
lean_dec_ref(v___y_6177_);
lean_dec(v___y_6176_);
lean_dec_ref(v___y_6175_);
lean_dec(v___y_6174_);
lean_dec_ref(v___y_6173_);
lean_dec(v___y_6172_);
lean_dec(v___y_6171_);
lean_dec_ref(v___y_6170_);
return v_res_6182_;
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
