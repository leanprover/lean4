// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Prover.Basic
// Imports: public import Lean.Meta.Tactic.BVDecide.Reflect public import Lean.Meta.Tactic.BVDecide.Counterexample public import Lean.Meta.Tactic.BVDecide.LRAT.Cert import Lean.Meta.Sym.SymM import Lean.Meta.Sym.Util
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_Gate_toString(uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ShareCommon_shareCommon___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 443, .m_capacity = 443, .m_length = 442, .m_data = "None of the hypotheses are in the supported BitVec fragment after applying preprocessing.\nThere are three potential reasons for this:\n1. If you are using custom BitVec constructs simplify them to built-in ones.\n2. If your problem is using only built-in ones it might currently be out of reach.\n   Consider expressing it in terms of different operations that are better supported.\n3. The original goal was reduced to False and is thus invalid."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Reflecting goal into BVLogicalExpr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___boxed(lean_object**);
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__0_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__3_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__4_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__5_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "(if "};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Reflected bv logical expression: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed(lean_object**);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed, .m_arity = 14, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___boxed(lean_object**);
lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(lean_object* v_f_1_, lean_object* v_x_2_, lean_object* v_g_3_, lean_object* v_r_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_18_; 
lean_inc(v_a_16_);
lean_inc_ref(v_a_15_);
lean_inc(v_a_14_);
lean_inc_ref(v_a_13_);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc(v_a_7_);
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
v___x_18_ = lean_apply_15(v_x_2_, v_g_3_, v_r_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, lean_box(0));
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_46_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_46_ == 0)
{
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_46_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_46_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
if (lean_obj_tag(v_a_19_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_33_; 
lean_dec(v_f_1_);
v_a_23_ = lean_ctor_get(v_a_19_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v_a_19_);
if (v_isSharedCheck_33_ == 0)
{
v___x_25_ = v_a_19_;
v_isShared_26_ = v_isSharedCheck_33_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v_a_19_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_33_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_a_23_);
v___x_28_ = v_reuseFailAlloc_32_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_30_; 
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_28_);
v___x_30_ = v___x_21_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
else
{
lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_45_; 
v_a_34_ = lean_ctor_get(v_a_19_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v_a_19_);
if (v_isSharedCheck_45_ == 0)
{
v___x_36_ = v_a_19_;
v_isShared_37_ = v_isSharedCheck_45_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v_a_19_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_45_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_38_ = lean_apply_1(v_f_1_, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_44_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_42_; 
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_40_);
v___x_42_ = v___x_21_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
}
else
{
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_54_; 
lean_dec(v_f_1_);
v_a_47_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_54_ == 0)
{
v___x_49_ = v___x_18_;
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_18_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_52_; 
if (v_isShared_50_ == 0)
{
v___x_52_ = v___x_49_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_a_47_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v_g_3_ = stack[2].m_obj;
lean_object* v_r_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_a_10_ = stack[9].m_obj;
lean_object* v_a_11_ = stack[10].m_obj;
lean_object* v_a_12_ = stack[11].m_obj;
lean_object* v_a_13_ = stack[12].m_obj;
lean_object* v_a_14_ = stack[13].m_obj;
lean_object* v_a_15_ = stack[14].m_obj;
lean_object* v_a_16_ = stack[15].m_obj;
lean_object* v_res_55_;
v_res_55_ = l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(v_f_1_, v_x_2_, v_g_3_, v_r_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg___boxed(lean_object** _args){
lean_object* v_f_56_ = _args[0];
lean_object* v_x_57_ = _args[1];
lean_object* v_g_58_ = _args[2];
lean_object* v_r_59_ = _args[3];
lean_object* v_a_60_ = _args[4];
lean_object* v_a_61_ = _args[5];
lean_object* v_a_62_ = _args[6];
lean_object* v_a_63_ = _args[7];
lean_object* v_a_64_ = _args[8];
lean_object* v_a_65_ = _args[9];
lean_object* v_a_66_ = _args[10];
lean_object* v_a_67_ = _args[11];
lean_object* v_a_68_ = _args[12];
lean_object* v_a_69_ = _args[13];
lean_object* v_a_70_ = _args[14];
lean_object* v_a_71_ = _args[15];
lean_object* v_a_72_ = _args[16];
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(v_f_56_, v_x_57_, v_g_58_, v_r_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
return v_res_73_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map(lean_object* v_00_u03b1_74_, lean_object* v_00_u03b2_75_, lean_object* v_f_76_, lean_object* v_x_77_, lean_object* v_g_78_, lean_object* v_r_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(v_f_76_, v_x_77_, v_g_78_, v_r_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
return v___x_93_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_UnsatProver_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_76_ = stack[2].m_obj;
lean_object* v_x_77_ = stack[3].m_obj;
lean_object* v_g_78_ = stack[4].m_obj;
lean_object* v_r_79_ = stack[5].m_obj;
lean_object* v_a_80_ = stack[6].m_obj;
lean_object* v_a_81_ = stack[7].m_obj;
lean_object* v_a_82_ = stack[8].m_obj;
lean_object* v_a_83_ = stack[9].m_obj;
lean_object* v_a_84_ = stack[10].m_obj;
lean_object* v_a_85_ = stack[11].m_obj;
lean_object* v_a_86_ = stack[12].m_obj;
lean_object* v_a_87_ = stack[13].m_obj;
lean_object* v_a_88_ = stack[14].m_obj;
lean_object* v_a_89_ = stack[15].m_obj;
lean_object* v_a_90_ = stack[16].m_obj;
lean_object* v_a_91_ = stack[17].m_obj;
lean_object* v_res_94_;
v_res_94_ = l_Lean_Meta_Tactic_BVDecide_UnsatProver_map(lean_box(0), lean_box(0), v_f_76_, v_x_77_, v_g_78_, v_r_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
stack->m_obj
 = v_res_94_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___boxed(lean_object** _args){
lean_object* v_00_u03b1_95_ = _args[0];
lean_object* v_00_u03b2_96_ = _args[1];
lean_object* v_f_97_ = _args[2];
lean_object* v_x_98_ = _args[3];
lean_object* v_g_99_ = _args[4];
lean_object* v_r_100_ = _args[5];
lean_object* v_a_101_ = _args[6];
lean_object* v_a_102_ = _args[7];
lean_object* v_a_103_ = _args[8];
lean_object* v_a_104_ = _args[9];
lean_object* v_a_105_ = _args[10];
lean_object* v_a_106_ = _args[11];
lean_object* v_a_107_ = _args[12];
lean_object* v_a_108_ = _args[13];
lean_object* v_a_109_ = _args[14];
lean_object* v_a_110_ = _args[15];
lean_object* v_a_111_ = _args[16];
lean_object* v_a_112_ = _args[17];
lean_object* v_a_113_ = _args[18];
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Meta_Tactic_BVDecide_UnsatProver_map(v_00_u03b1_95_, v_00_u03b2_96_, v_f_97_, v_x_98_, v_g_99_, v_r_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
return v_res_114_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0(lean_object* v_x_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v___x_128_; 
lean_inc(v___y_122_);
lean_inc_ref(v___y_121_);
lean_inc(v___y_120_);
lean_inc_ref(v___y_119_);
lean_inc(v___y_118_);
lean_inc(v___y_117_);
lean_inc_ref(v___y_116_);
v___x_128_ = lean_apply_12(v_x_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, lean_box(0));
return v___x_128_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_115_ = stack[0].m_obj;
lean_object* v___y_116_ = stack[1].m_obj;
lean_object* v___y_117_ = stack[2].m_obj;
lean_object* v___y_118_ = stack[3].m_obj;
lean_object* v___y_119_ = stack[4].m_obj;
lean_object* v___y_120_ = stack[5].m_obj;
lean_object* v___y_121_ = stack[6].m_obj;
lean_object* v___y_122_ = stack[7].m_obj;
lean_object* v___y_123_ = stack[8].m_obj;
lean_object* v___y_124_ = stack[9].m_obj;
lean_object* v___y_125_ = stack[10].m_obj;
lean_object* v___y_126_ = stack[11].m_obj;
lean_object* v_res_129_;
v_res_129_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0(v_x_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
stack->m_obj
 = v_res_129_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0___boxed(lean_object* v_x_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0(v_x_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_143_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(lean_object* v_mvarId_144_, lean_object* v_x_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___f_158_; lean_object* v___x_159_; 
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
lean_inc(v___y_148_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
v___f_158_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_158_, 0, v_x_145_);
lean_closure_set(v___f_158_, 1, v___y_146_);
lean_closure_set(v___f_158_, 2, v___y_147_);
lean_closure_set(v___f_158_, 3, v___y_148_);
lean_closure_set(v___f_158_, 4, v___y_149_);
lean_closure_set(v___f_158_, 5, v___y_150_);
lean_closure_set(v___f_158_, 6, v___y_151_);
lean_closure_set(v___f_158_, 7, v___y_152_);
v___x_159_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_144_, v___f_158_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
if (lean_obj_tag(v___x_159_) == 0)
{
return v___x_159_;
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_144_ = stack[0].m_obj;
lean_object* v_x_145_ = stack[1].m_obj;
lean_object* v___y_146_ = stack[2].m_obj;
lean_object* v___y_147_ = stack[3].m_obj;
lean_object* v___y_148_ = stack[4].m_obj;
lean_object* v___y_149_ = stack[5].m_obj;
lean_object* v___y_150_ = stack[6].m_obj;
lean_object* v___y_151_ = stack[7].m_obj;
lean_object* v___y_152_ = stack[8].m_obj;
lean_object* v___y_153_ = stack[9].m_obj;
lean_object* v___y_154_ = stack[10].m_obj;
lean_object* v___y_155_ = stack[11].m_obj;
lean_object* v___y_156_ = stack[12].m_obj;
lean_object* v_res_168_;
v_res_168_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_mvarId_144_, v_x_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___boxed(lean_object* v_mvarId_169_, lean_object* v_x_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_mvarId_169_, v_x_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_183_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(lean_object* v_00_u03b1_184_, lean_object* v_mvarId_185_, lean_object* v_x_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_mvarId_185_, v_x_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
return v___x_199_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_185_ = stack[1].m_obj;
lean_object* v_x_186_ = stack[2].m_obj;
lean_object* v___y_187_ = stack[3].m_obj;
lean_object* v___y_188_ = stack[4].m_obj;
lean_object* v___y_189_ = stack[5].m_obj;
lean_object* v___y_190_ = stack[6].m_obj;
lean_object* v___y_191_ = stack[7].m_obj;
lean_object* v___y_192_ = stack[8].m_obj;
lean_object* v___y_193_ = stack[9].m_obj;
lean_object* v___y_194_ = stack[10].m_obj;
lean_object* v___y_195_ = stack[11].m_obj;
lean_object* v___y_196_ = stack[12].m_obj;
lean_object* v___y_197_ = stack[13].m_obj;
lean_object* v_res_200_;
v_res_200_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(lean_box(0), v_mvarId_185_, v_x_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
stack->m_obj
 = v_res_200_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___boxed(lean_object* v_00_u03b1_201_, lean_object* v_mvarId_202_, lean_object* v_x_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(v_00_u03b1_201_, v_mvarId_202_, v_x_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
return v_res_216_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(lean_object* v_msgData_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; lean_object* v_env_224_; uint8_t v___x_225_; lean_object* v_env_226_; lean_object* v___x_227_; lean_object* v_toCold_228_; lean_object* v_mctx_229_; lean_object* v_lctx_230_; lean_object* v_options_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_223_ = lean_st_ref_get(v___y_221_);
v_env_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc_ref(v_env_224_);
lean_dec(v___x_223_);
v___x_225_ = 0;
v_env_226_ = l_Lean_Environment_setRecordingDeps(v_env_224_, v___x_225_);
v___x_227_ = lean_st_ref_get(v___y_219_);
v_toCold_228_ = lean_ctor_get(v___y_220_, 0);
v_mctx_229_ = lean_ctor_get(v___x_227_, 0);
lean_inc_ref(v_mctx_229_);
lean_dec(v___x_227_);
v_lctx_230_ = lean_ctor_get(v___y_218_, 2);
v_options_231_ = lean_ctor_get(v_toCold_228_, 2);
lean_inc_ref(v_options_231_);
lean_inc_ref(v_lctx_230_);
v___x_232_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_232_, 0, v_env_226_);
lean_ctor_set(v___x_232_, 1, v_mctx_229_);
lean_ctor_set(v___x_232_, 2, v_lctx_230_);
lean_ctor_set(v___x_232_, 3, v_options_231_);
v___x_233_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v_msgData_217_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_217_ = stack[0].m_obj;
lean_object* v___y_218_ = stack[1].m_obj;
lean_object* v___y_219_ = stack[2].m_obj;
lean_object* v___y_220_ = stack[3].m_obj;
lean_object* v___y_221_ = stack[4].m_obj;
lean_object* v_res_235_;
v_res_235_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msgData_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
stack->m_obj
 = v_res_235_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5___boxed(lean_object* v_msgData_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msgData_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
return v_res_242_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(lean_object* v_msg_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_ref_249_; lean_object* v___x_250_; lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_259_; 
v_ref_249_ = lean_ctor_get(v___y_246_, 2);
v___x_250_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_259_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
lean_inc(v_ref_249_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_ref_249_);
lean_ctor_set(v___x_255_, 1, v_a_251_);
if (v_isShared_254_ == 0)
{
lean_ctor_set_tag(v___x_253_, 1);
lean_ctor_set(v___x_253_, 0, v___x_255_);
v___x_257_ = v___x_253_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_243_ = stack[0].m_obj;
lean_object* v___y_244_ = stack[1].m_obj;
lean_object* v___y_245_ = stack[2].m_obj;
lean_object* v___y_246_ = stack[3].m_obj;
lean_object* v___y_247_ = stack[4].m_obj;
lean_object* v_res_260_;
v_res_260_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg___boxed(lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_267_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(lean_object* v_a_268_, lean_object* v_x_269_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
uint8_t v___x_270_; 
v___x_270_ = 0;
return v___x_270_;
}
else
{
lean_object* v_key_271_; lean_object* v_tail_272_; lean_object* v_type_273_; lean_object* v_type_274_; uint8_t v___x_275_; 
v_key_271_ = lean_ctor_get(v_x_269_, 0);
v_tail_272_ = lean_ctor_get(v_x_269_, 2);
v_type_273_ = lean_ctor_get(v_key_271_, 1);
v_type_274_ = lean_ctor_get(v_a_268_, 1);
v___x_275_ = lean_expr_eqv(v_type_273_, v_type_274_);
if (v___x_275_ == 0)
{
v_x_269_ = v_tail_272_;
goto _start;
}
else
{
return v___x_275_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_268_ = stack[0].m_obj;
lean_object* v_x_269_ = stack[1].m_obj;
uint8_t v_res_277_;
v_res_277_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_268_, v_x_269_);
stack->m_num = v_res_277_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg___boxed(lean_object* v_a_278_, lean_object* v_x_279_){
_start:
{
uint8_t v_res_280_; lean_object* v_r_281_; 
v_res_280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_278_, v_x_279_);
lean_dec(v_x_279_);
lean_dec_ref(v_a_278_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
return v_x_282_;
}
else
{
lean_object* v_key_284_; lean_object* v_value_285_; lean_object* v_tail_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_310_; 
v_key_284_ = lean_ctor_get(v_x_283_, 0);
v_value_285_ = lean_ctor_get(v_x_283_, 1);
v_tail_286_ = lean_ctor_get(v_x_283_, 2);
v_isSharedCheck_310_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_310_ == 0)
{
v___x_288_ = v_x_283_;
v_isShared_289_ = v_isSharedCheck_310_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_tail_286_);
lean_inc(v_value_285_);
lean_inc(v_key_284_);
lean_dec(v_x_283_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_310_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_type_290_; lean_object* v___x_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v___x_294_; uint64_t v_fold_295_; uint64_t v___x_296_; uint64_t v___x_297_; uint64_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; size_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
v_type_290_ = lean_ctor_get(v_key_284_, 1);
v___x_291_ = lean_array_get_size(v_x_282_);
v___x_292_ = l_Lean_Expr_hash(v_type_290_);
v___x_293_ = 32ULL;
v___x_294_ = lean_uint64_shift_right(v___x_292_, v___x_293_);
v_fold_295_ = lean_uint64_xor(v___x_292_, v___x_294_);
v___x_296_ = 16ULL;
v___x_297_ = lean_uint64_shift_right(v_fold_295_, v___x_296_);
v___x_298_ = lean_uint64_xor(v_fold_295_, v___x_297_);
v___x_299_ = lean_uint64_to_usize(v___x_298_);
v___x_300_ = lean_usize_of_nat(v___x_291_);
v___x_301_ = ((size_t)1ULL);
v___x_302_ = lean_usize_sub(v___x_300_, v___x_301_);
v___x_303_ = lean_usize_land(v___x_299_, v___x_302_);
v___x_304_ = lean_array_uget_borrowed(v_x_282_, v___x_303_);
lean_inc(v___x_304_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 2, v___x_304_);
v___x_306_ = v___x_288_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_key_284_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_value_285_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v___x_304_);
v___x_306_ = v_reuseFailAlloc_309_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; 
v___x_307_ = lean_array_uset(v_x_282_, v___x_303_, v___x_306_);
v_x_282_ = v___x_307_;
v_x_283_ = v_tail_286_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(lean_object* v_i_311_, lean_object* v_source_312_, lean_object* v_target_313_){
_start:
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = lean_array_get_size(v_source_312_);
v___x_315_ = lean_nat_dec_lt(v_i_311_, v___x_314_);
if (v___x_315_ == 0)
{
lean_dec_ref(v_source_312_);
lean_dec(v_i_311_);
return v_target_313_;
}
else
{
lean_object* v_es_316_; lean_object* v___x_317_; lean_object* v_source_318_; lean_object* v_target_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_es_316_ = lean_array_fget(v_source_312_, v_i_311_);
v___x_317_ = lean_box(0);
v_source_318_ = lean_array_fset(v_source_312_, v_i_311_, v___x_317_);
v_target_319_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(v_target_313_, v_es_316_);
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_add(v_i_311_, v___x_320_);
lean_dec(v_i_311_);
v_i_311_ = v___x_321_;
v_source_312_ = v_source_318_;
v_target_313_ = v_target_319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(lean_object* v_data_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_nbuckets_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_324_ = lean_array_get_size(v_data_323_);
v___x_325_ = lean_unsigned_to_nat(2u);
v_nbuckets_326_ = lean_nat_mul(v___x_324_, v___x_325_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_box(0);
v___x_329_ = lean_mk_array(v_nbuckets_326_, v___x_328_);
v___x_330_ = lean_array_propagate_mark(v_data_323_, v___x_329_);
v___x_331_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v___x_327_, v_data_323_, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(lean_object* v_m_332_, lean_object* v_a_333_, lean_object* v_b_334_){
_start:
{
lean_object* v_size_335_; lean_object* v_buckets_336_; lean_object* v_type_337_; lean_object* v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v_fold_342_; uint64_t v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; lean_object* v_bkt_351_; uint8_t v___x_352_; 
v_size_335_ = lean_ctor_get(v_m_332_, 0);
v_buckets_336_ = lean_ctor_get(v_m_332_, 1);
v_type_337_ = lean_ctor_get(v_a_333_, 1);
v___x_338_ = lean_array_get_size(v_buckets_336_);
v___x_339_ = l_Lean_Expr_hash(v_type_337_);
v___x_340_ = 32ULL;
v___x_341_ = lean_uint64_shift_right(v___x_339_, v___x_340_);
v_fold_342_ = lean_uint64_xor(v___x_339_, v___x_341_);
v___x_343_ = 16ULL;
v___x_344_ = lean_uint64_shift_right(v_fold_342_, v___x_343_);
v___x_345_ = lean_uint64_xor(v_fold_342_, v___x_344_);
v___x_346_ = lean_uint64_to_usize(v___x_345_);
v___x_347_ = lean_usize_of_nat(v___x_338_);
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_sub(v___x_347_, v___x_348_);
v___x_350_ = lean_usize_land(v___x_346_, v___x_349_);
v_bkt_351_ = lean_array_uget_borrowed(v_buckets_336_, v___x_350_);
v___x_352_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_333_, v_bkt_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_373_; 
lean_inc_ref(v_buckets_336_);
lean_inc(v_size_335_);
v_isSharedCheck_373_ = !lean_is_exclusive(v_m_332_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; lean_object* v_unused_375_; 
v_unused_374_ = lean_ctor_get(v_m_332_, 1);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_m_332_, 0);
lean_dec(v_unused_375_);
v___x_354_ = v_m_332_;
v_isShared_355_ = v_isSharedCheck_373_;
goto v_resetjp_353_;
}
else
{
lean_dec(v_m_332_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_373_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v_size_x27_357_; lean_object* v___x_358_; lean_object* v_buckets_x27_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_356_ = lean_unsigned_to_nat(1u);
v_size_x27_357_ = lean_nat_add(v_size_335_, v___x_356_);
lean_dec(v_size_335_);
lean_inc(v_bkt_351_);
v___x_358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_358_, 0, v_a_333_);
lean_ctor_set(v___x_358_, 1, v_b_334_);
lean_ctor_set(v___x_358_, 2, v_bkt_351_);
v_buckets_x27_359_ = lean_array_uset(v_buckets_336_, v___x_350_, v___x_358_);
v___x_360_ = lean_unsigned_to_nat(4u);
v___x_361_ = lean_nat_mul(v_size_x27_357_, v___x_360_);
v___x_362_ = lean_unsigned_to_nat(3u);
v___x_363_ = lean_nat_div(v___x_361_, v___x_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_array_get_size(v_buckets_x27_359_);
v___x_365_ = lean_nat_dec_le(v___x_363_, v___x_364_);
lean_dec(v___x_363_);
if (v___x_365_ == 0)
{
lean_object* v_val_366_; lean_object* v___x_368_; 
v_val_366_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_buckets_x27_359_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v_val_366_);
lean_ctor_set(v___x_354_, 0, v_size_x27_357_);
v___x_368_ = v___x_354_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_size_x27_357_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_val_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
else
{
lean_object* v___x_371_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v_buckets_x27_359_);
lean_ctor_set(v___x_354_, 0, v_size_x27_357_);
v___x_371_ = v___x_354_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_size_x27_357_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_buckets_x27_359_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_dec(v_b_334_);
lean_dec_ref(v_a_333_);
return v_m_332_;
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_box(0);
v___x_380_ = lean_unsigned_to_nat(16u);
v___x_381_ = lean_mk_array(v___x_380_, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4(void){
_start:
{
lean_object* v___x_385_; lean_object* v_sats_386_; lean_object* v___x_387_; 
v___x_385_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3);
v_sats_386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0));
v___x_387_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_387_, 0, v_sats_386_);
lean_ctor_set(v___x_387_, 1, v___x_385_);
lean_ctor_set(v___x_387_, 2, v___x_385_);
lean_ctor_set(v___x_387_, 3, v___x_385_);
return v___x_387_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(lean_object* v_as_388_, size_t v_sz_389_, size_t v_i_390_, lean_object* v_b_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_a_405_; uint8_t v___x_409_; 
v___x_409_ = lean_usize_dec_lt(v_i_390_, v_sz_389_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v_b_391_);
return v___x_410_;
}
else
{
lean_object* v_fst_411_; lean_object* v_snd_412_; lean_object* v_a_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_fst_411_ = lean_ctor_get(v_b_391_, 0);
lean_inc(v_fst_411_);
v_snd_412_ = lean_ctor_get(v_b_391_, 1);
lean_inc(v_snd_412_);
lean_dec_ref(v_b_391_);
v_a_413_ = lean_array_uget_borrowed(v_as_388_, v_i_390_);
v___x_414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1));
v___x_415_ = l_Lean_Core_checkSystem(v___x_414_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec_ref_known(v___x_415_, 1);
lean_inc(v_a_413_);
v___x_416_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed), 14, 1);
lean_closure_set(v___x_416_, 0, v_a_413_);
v___x_417_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4);
v___x_418_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v___x_416_, v___x_417_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v_fst_420_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
v_fst_420_ = lean_ctor_get(v_a_419_, 0);
if (lean_obj_tag(v_fst_420_) == 1)
{
lean_object* v_snd_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_431_; 
lean_inc_ref(v_fst_420_);
v_snd_421_ = lean_ctor_get(v_a_419_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_a_419_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v_a_419_, 0);
lean_dec(v_unused_432_);
v___x_423_ = v_a_419_;
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_snd_421_);
lean_dec(v_a_419_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_val_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v_val_425_ = lean_ctor_get(v_fst_420_, 0);
lean_inc(v_val_425_);
lean_dec_ref_known(v_fst_420_, 1);
v___x_426_ = l_Array_append___redArg(v_fst_411_, v_snd_421_);
lean_dec(v_snd_421_);
v___x_427_ = lean_array_push(v___x_426_, v_val_425_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v_snd_412_);
lean_ctor_set(v___x_423_, 0, v___x_427_);
v___x_429_ = v___x_423_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_snd_412_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
v_a_405_ = v___x_429_;
goto v___jp_404_;
}
}
}
else
{
lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_441_; 
v_isSharedCheck_441_ = !lean_is_exclusive(v_a_419_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; lean_object* v_unused_443_; 
v_unused_442_ = lean_ctor_get(v_a_419_, 1);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_a_419_, 0);
lean_dec(v_unused_443_);
v___x_434_ = v_a_419_;
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
else
{
lean_dec(v_a_419_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_436_ = lean_box(0);
lean_inc(v_a_413_);
v___x_437_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_snd_412_, v_a_413_, v___x_436_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_437_);
lean_ctor_set(v___x_434_, 0, v_fst_411_);
v___x_439_ = v___x_434_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_fst_411_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
v_a_405_ = v___x_439_;
goto v___jp_404_;
}
}
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_dec(v_snd_412_);
lean_dec(v_fst_411_);
v_a_444_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_418_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_418_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec(v_snd_412_);
lean_dec(v_fst_411_);
v_a_452_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_415_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_415_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
v___jp_404_:
{
size_t v___x_406_; size_t v___x_407_; 
v___x_406_ = ((size_t)1ULL);
v___x_407_ = lean_usize_add(v_i_390_, v___x_406_);
v_i_390_ = v___x_407_;
v_b_391_ = v_a_405_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_388_ = stack[0].m_obj;
size_t v_sz_389_ = stack[1].m_num;
size_t v_i_390_ = stack[2].m_num;
lean_object* v_b_391_ = stack[3].m_obj;
lean_object* v___y_392_ = stack[4].m_obj;
lean_object* v___y_393_ = stack[5].m_obj;
lean_object* v___y_394_ = stack[6].m_obj;
lean_object* v___y_395_ = stack[7].m_obj;
lean_object* v___y_396_ = stack[8].m_obj;
lean_object* v___y_397_ = stack[9].m_obj;
lean_object* v___y_398_ = stack[10].m_obj;
lean_object* v___y_399_ = stack[11].m_obj;
lean_object* v___y_400_ = stack[12].m_obj;
lean_object* v___y_401_ = stack[13].m_obj;
lean_object* v___y_402_ = stack[14].m_obj;
lean_object* v_res_460_;
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v_as_388_, v_sz_389_, v_i_390_, v_b_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
stack->m_obj
 = v_res_460_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___boxed(lean_object* v_as_461_, lean_object* v_sz_462_, lean_object* v_i_463_, lean_object* v_b_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
size_t v_sz_boxed_477_; size_t v_i_boxed_478_; lean_object* v_res_479_; 
v_sz_boxed_477_ = lean_unbox_usize(v_sz_462_);
lean_dec(v_sz_462_);
v_i_boxed_478_ = lean_unbox_usize(v_i_463_);
lean_dec(v_i_463_);
v_res_479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v_as_461_, v_sz_boxed_477_, v_i_boxed_478_, v_b_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec_ref(v_as_461_);
return v_res_479_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(lean_object* v_a_480_, lean_object* v_b_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_array_489_; lean_object* v_start_490_; lean_object* v_stop_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_506_; 
v_array_489_ = lean_ctor_get(v_a_480_, 0);
v_start_490_ = lean_ctor_get(v_a_480_, 1);
v_stop_491_ = lean_ctor_get(v_a_480_, 2);
v_isSharedCheck_506_ = !lean_is_exclusive(v_a_480_);
if (v_isSharedCheck_506_ == 0)
{
v___x_493_ = v_a_480_;
v_isShared_494_ = v_isSharedCheck_506_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_stop_491_);
lean_inc(v_start_490_);
lean_inc(v_array_489_);
lean_dec(v_a_480_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_506_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
uint8_t v___x_495_; 
v___x_495_ = lean_nat_dec_lt(v_start_490_, v_stop_491_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; 
lean_del_object(v___x_493_);
lean_dec(v_stop_491_);
lean_dec(v_start_490_);
lean_dec_ref(v_array_489_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v_b_481_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = lean_nat_add(v_start_490_, v___x_497_);
lean_inc_ref(v_array_489_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_498_);
v___x_500_ = v___x_493_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_array_489_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_stop_491_);
v___x_500_ = v_reuseFailAlloc_505_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_array_fget(v_array_489_, v_start_490_);
lean_dec(v_start_490_);
lean_dec_ref(v_array_489_);
v___x_502_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_b_481_, v___x_501_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
v_a_480_ = v___x_500_;
v_b_481_ = v_a_503_;
goto _start;
}
else
{
lean_dec_ref(v___x_500_);
return v___x_502_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_480_ = stack[0].m_obj;
lean_object* v_b_481_ = stack[1].m_obj;
lean_object* v___y_482_ = stack[2].m_obj;
lean_object* v___y_483_ = stack[3].m_obj;
lean_object* v___y_484_ = stack[4].m_obj;
lean_object* v___y_485_ = stack[5].m_obj;
lean_object* v___y_486_ = stack[6].m_obj;
lean_object* v___y_487_ = stack[7].m_obj;
lean_object* v_res_507_;
v_res_507_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_480_, v_b_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg___boxed(lean_object* v_a_508_, lean_object* v_b_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_508_, v_b_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
return v_res_517_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1));
v___x_522_ = l_Lean_MessageData_ofFormat(v___x_521_);
return v___x_522_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(lean_object* v_sats_523_, lean_object* v_unusedHypotheses_524_, lean_object* v___x_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_hypotheses_538_; lean_object* v___x_539_; size_t v_sz_540_; size_t v___x_541_; lean_object* v___x_542_; 
v_hypotheses_538_ = lean_ctor_get(v___y_526_, 0);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v_sats_523_);
lean_ctor_set(v___x_539_, 1, v_unusedHypotheses_524_);
v_sz_540_ = lean_array_size(v_hypotheses_538_);
v___x_541_ = ((size_t)0ULL);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v_hypotheses_538_, v_sz_540_, v___x_541_, v___x_539_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v_fst_544_; lean_object* v_snd_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_587_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___x_542_, 1);
v_fst_544_ = lean_ctor_get(v_a_543_, 0);
v_snd_545_ = lean_ctor_get(v_a_543_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_a_543_);
if (v_isSharedCheck_587_ == 0)
{
v___x_547_ = v_a_543_;
v_isShared_548_ = v_isSharedCheck_587_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_snd_545_);
lean_inc(v_fst_544_);
lean_dec(v_a_543_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_587_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = lean_array_get_size(v_fst_544_);
v___x_550_ = lean_nat_dec_eq(v___x_549_, v___x_525_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_551_ = lean_array_fget(v_fst_544_, v___x_525_);
v___x_552_ = lean_unsigned_to_nat(1u);
v___x_553_ = l_Array_toSubarray___redArg(v_fst_544_, v___x_552_, v___x_549_);
v___x_554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v___x_553_, v___x_551_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_576_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_576_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_576_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_576_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_bvExpr_559_; lean_object* v_satAtAtoms_560_; lean_object* v_expr_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_575_; 
v_bvExpr_559_ = lean_ctor_get(v_a_555_, 0);
v_satAtAtoms_560_ = lean_ctor_get(v_a_555_, 1);
v_expr_561_ = lean_ctor_get(v_a_555_, 2);
v_isSharedCheck_575_ = !lean_is_exclusive(v_a_555_);
if (v_isSharedCheck_575_ == 0)
{
v___x_563_ = v_a_555_;
v_isShared_564_ = v_isSharedCheck_575_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_expr_561_);
lean_inc(v_satAtAtoms_560_);
lean_inc(v_bvExpr_559_);
lean_dec(v_a_555_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_575_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = l_Lean_ShareCommon_shareCommon___redArg(v_bvExpr_559_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_565_);
v___x_567_ = v___x_563_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_satAtAtoms_560_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v_expr_561_);
v___x_567_ = v_reuseFailAlloc_574_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_569_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_567_);
v___x_569_ = v___x_547_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_snd_545_);
v___x_569_ = v_reuseFailAlloc_573_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_571_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_569_);
v___x_571_ = v___x_557_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
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
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_del_object(v___x_547_);
lean_dec(v_snd_545_);
v_a_577_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_554_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_554_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; 
lean_del_object(v___x_547_);
lean_dec(v_snd_545_);
lean_dec(v_fst_544_);
v___x_585_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2);
v___x_586_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v___x_585_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
return v___x_586_;
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_a_588_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_542_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_542_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_sats_523_ = stack[0].m_obj;
lean_object* v_unusedHypotheses_524_ = stack[1].m_obj;
lean_object* v___x_525_ = stack[2].m_obj;
lean_object* v___y_526_ = stack[3].m_obj;
lean_object* v___y_527_ = stack[4].m_obj;
lean_object* v___y_528_ = stack[5].m_obj;
lean_object* v___y_529_ = stack[6].m_obj;
lean_object* v___y_530_ = stack[7].m_obj;
lean_object* v___y_531_ = stack[8].m_obj;
lean_object* v___y_532_ = stack[9].m_obj;
lean_object* v___y_533_ = stack[10].m_obj;
lean_object* v___y_534_ = stack[11].m_obj;
lean_object* v___y_535_ = stack[12].m_obj;
lean_object* v___y_536_ = stack[13].m_obj;
lean_object* v_res_596_;
v_res_596_ = l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(v_sats_523_, v_unusedHypotheses_524_, v___x_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
stack->m_obj
 = v_res_596_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed(lean_object* v_sats_597_, lean_object* v_unusedHypotheses_598_, lean_object* v___x_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(v_sats_597_, v_unusedHypotheses_598_, v___x_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___x_599_);
return v_res_612_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_box(0);
v___x_614_ = lean_unsigned_to_nat(16u);
v___x_615_ = lean_mk_array(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v_unusedHypotheses_618_; 
v___x_616_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0);
v___x_617_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_unusedHypotheses_618_, 0, v___x_617_);
lean_ctor_set(v_unusedHypotheses_618_, 1, v___x_616_);
return v_unusedHypotheses_618_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2(void){
_start:
{
lean_object* v___x_619_; lean_object* v_unusedHypotheses_620_; lean_object* v_sats_621_; lean_object* v___f_622_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_620_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1);
v_sats_621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0));
v___f_622_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed), 15, 3);
lean_closure_set(v___f_622_, 0, v_sats_621_);
lean_closure_set(v___f_622_, 1, v_unusedHypotheses_620_);
lean_closure_set(v___f_622_, 2, v___x_619_);
return v___f_622_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV(lean_object* v_g_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___f_636_; lean_object* v___x_637_; 
v___f_636_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2);
v___x_637_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_g_623_, v___f_636_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_637_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_reflectBV_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_623_ = stack[0].m_obj;
lean_object* v_a_624_ = stack[1].m_obj;
lean_object* v_a_625_ = stack[2].m_obj;
lean_object* v_a_626_ = stack[3].m_obj;
lean_object* v_a_627_ = stack[4].m_obj;
lean_object* v_a_628_ = stack[5].m_obj;
lean_object* v_a_629_ = stack[6].m_obj;
lean_object* v_a_630_ = stack[7].m_obj;
lean_object* v_a_631_ = stack[8].m_obj;
lean_object* v_a_632_ = stack[9].m_obj;
lean_object* v_a_633_ = stack[10].m_obj;
lean_object* v_a_634_ = stack[11].m_obj;
lean_object* v_res_638_;
v_res_638_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
stack->m_obj
 = v_res_638_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___boxed(lean_object* v_g_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0(lean_object* v_00_u03b2_653_, lean_object* v_m_654_, lean_object* v_a_655_, lean_object* v_b_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_m_654_, v_a_655_, v_b_656_);
return v___x_657_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(lean_object* v_inst_658_, lean_object* v_R_659_, lean_object* v_a_660_, lean_object* v_b_661_, lean_object* v_c_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_660_, v_b_661_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
return v___x_675_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_660_ = stack[2].m_obj;
lean_object* v_b_661_ = stack[3].m_obj;
lean_object* v___y_663_ = stack[5].m_obj;
lean_object* v___y_664_ = stack[6].m_obj;
lean_object* v___y_665_ = stack[7].m_obj;
lean_object* v___y_666_ = stack[8].m_obj;
lean_object* v___y_667_ = stack[9].m_obj;
lean_object* v___y_668_ = stack[10].m_obj;
lean_object* v___y_669_ = stack[11].m_obj;
lean_object* v___y_670_ = stack[12].m_obj;
lean_object* v___y_671_ = stack[13].m_obj;
lean_object* v___y_672_ = stack[14].m_obj;
lean_object* v___y_673_ = stack[15].m_obj;
lean_object* v_res_676_;
v_res_676_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(lean_box(0), lean_box(0), v_a_660_, v_b_661_, lean_box(0), v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
stack->m_obj
 = v_res_676_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___boxed(lean_object** _args){
lean_object* v_inst_677_ = _args[0];
lean_object* v_R_678_ = _args[1];
lean_object* v_a_679_ = _args[2];
lean_object* v_b_680_ = _args[3];
lean_object* v_c_681_ = _args[4];
lean_object* v___y_682_ = _args[5];
lean_object* v___y_683_ = _args[6];
lean_object* v___y_684_ = _args[7];
lean_object* v___y_685_ = _args[8];
lean_object* v___y_686_ = _args[9];
lean_object* v___y_687_ = _args[10];
lean_object* v___y_688_ = _args[11];
lean_object* v___y_689_ = _args[12];
lean_object* v___y_690_ = _args[13];
lean_object* v___y_691_ = _args[14];
lean_object* v___y_692_ = _args[15];
lean_object* v___y_693_ = _args[16];
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(v_inst_677_, v_R_678_, v_a_679_, v_b_680_, v_c_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_694_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(lean_object* v_00_u03b1_695_, lean_object* v_msg_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_696_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
return v___x_709_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_696_ = stack[1].m_obj;
lean_object* v___y_697_ = stack[2].m_obj;
lean_object* v___y_698_ = stack[3].m_obj;
lean_object* v___y_699_ = stack[4].m_obj;
lean_object* v___y_700_ = stack[5].m_obj;
lean_object* v___y_701_ = stack[6].m_obj;
lean_object* v___y_702_ = stack[7].m_obj;
lean_object* v___y_703_ = stack[8].m_obj;
lean_object* v___y_704_ = stack[9].m_obj;
lean_object* v___y_705_ = stack[10].m_obj;
lean_object* v___y_706_ = stack[11].m_obj;
lean_object* v___y_707_ = stack[12].m_obj;
lean_object* v_res_710_;
v_res_710_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(lean_box(0), v_msg_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
stack->m_obj
 = v_res_710_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___boxed(lean_object* v_00_u03b1_711_, lean_object* v_msg_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(v_00_u03b1_711_, v_msg_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_725_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(lean_object* v_00_u03b2_726_, lean_object* v_a_727_, lean_object* v_x_728_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_727_, v_x_728_);
return v___x_729_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_727_ = stack[1].m_obj;
lean_object* v_x_728_ = stack[2].m_obj;
uint8_t v_res_730_;
v_res_730_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(lean_box(0), v_a_727_, v_x_728_);
stack->m_num = v_res_730_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___boxed(lean_object* v_00_u03b2_731_, lean_object* v_a_732_, lean_object* v_x_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(v_00_u03b2_731_, v_a_732_, v_x_733_);
lean_dec(v_x_733_);
lean_dec_ref(v_a_732_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1(lean_object* v_00_u03b2_736_, lean_object* v_data_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_data_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_739_, lean_object* v_i_740_, lean_object* v_source_741_, lean_object* v_target_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v_i_740_, v_source_741_, v_target_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_744_, lean_object* v_x_745_, lean_object* v_x_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(v_x_745_, v_x_746_);
return v___x_747_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = lean_unsigned_to_nat(32u);
v___x_749_ = lean_mk_empty_array_with_capacity(v___x_748_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_751_ = ((size_t)5ULL);
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = lean_unsigned_to_nat(32u);
v___x_754_ = lean_mk_empty_array_with_capacity(v___x_753_);
v___x_755_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0);
v___x_756_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v___x_754_);
lean_ctor_set(v___x_756_, 2, v___x_752_);
lean_ctor_set(v___x_756_, 3, v___x_752_);
lean_ctor_set_usize(v___x_756_, 4, v___x_751_);
return v___x_756_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; lean_object* v_traceState_760_; lean_object* v_traces_761_; lean_object* v___x_762_; lean_object* v_traceState_763_; lean_object* v_env_764_; lean_object* v_nextMacroScope_765_; lean_object* v_ngen_766_; lean_object* v_auxDeclNGen_767_; lean_object* v_cache_768_; lean_object* v_recordedDeps_769_; lean_object* v_messages_770_; lean_object* v_infoState_771_; lean_object* v_snapshotTasks_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_791_; 
v___x_759_ = lean_st_ref_get(v___y_757_);
v_traceState_760_ = lean_ctor_get(v___x_759_, 4);
lean_inc_ref(v_traceState_760_);
lean_dec(v___x_759_);
v_traces_761_ = lean_ctor_get(v_traceState_760_, 0);
lean_inc_ref(v_traces_761_);
lean_dec_ref(v_traceState_760_);
v___x_762_ = lean_st_ref_take(v___y_757_);
v_traceState_763_ = lean_ctor_get(v___x_762_, 4);
v_env_764_ = lean_ctor_get(v___x_762_, 0);
v_nextMacroScope_765_ = lean_ctor_get(v___x_762_, 1);
v_ngen_766_ = lean_ctor_get(v___x_762_, 2);
v_auxDeclNGen_767_ = lean_ctor_get(v___x_762_, 3);
v_cache_768_ = lean_ctor_get(v___x_762_, 5);
v_recordedDeps_769_ = lean_ctor_get(v___x_762_, 6);
v_messages_770_ = lean_ctor_get(v___x_762_, 7);
v_infoState_771_ = lean_ctor_get(v___x_762_, 8);
v_snapshotTasks_772_ = lean_ctor_get(v___x_762_, 9);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_791_ == 0)
{
v___x_774_ = v___x_762_;
v_isShared_775_ = v_isSharedCheck_791_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_snapshotTasks_772_);
lean_inc(v_infoState_771_);
lean_inc(v_messages_770_);
lean_inc(v_recordedDeps_769_);
lean_inc(v_cache_768_);
lean_inc(v_traceState_763_);
lean_inc(v_auxDeclNGen_767_);
lean_inc(v_ngen_766_);
lean_inc(v_nextMacroScope_765_);
lean_inc(v_env_764_);
lean_dec(v___x_762_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_791_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
uint64_t v_tid_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_789_; 
v_tid_776_ = lean_ctor_get_uint64(v_traceState_763_, sizeof(void*)*1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_traceState_763_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v_traceState_763_, 0);
lean_dec(v_unused_790_);
v___x_778_ = v_traceState_763_;
v_isShared_779_ = v_isSharedCheck_789_;
goto v_resetjp_777_;
}
else
{
lean_dec(v_traceState_763_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_789_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_780_);
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_780_);
lean_ctor_set_uint64(v_reuseFailAlloc_788_, sizeof(void*)*1, v_tid_776_);
v___x_782_ = v_reuseFailAlloc_788_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_784_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 4, v___x_782_);
v___x_784_ = v___x_774_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_env_764_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_nextMacroScope_765_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_ngen_766_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v_auxDeclNGen_767_);
lean_ctor_set(v_reuseFailAlloc_787_, 4, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_787_, 5, v_cache_768_);
lean_ctor_set(v_reuseFailAlloc_787_, 6, v_recordedDeps_769_);
lean_ctor_set(v_reuseFailAlloc_787_, 7, v_messages_770_);
lean_ctor_set(v_reuseFailAlloc_787_, 8, v_infoState_771_);
lean_ctor_set(v_reuseFailAlloc_787_, 9, v_snapshotTasks_772_);
v___x_784_ = v_reuseFailAlloc_787_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_st_ref_put(v___y_757_, v___x_784_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v_traces_761_);
return v___x_786_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_757_ = stack[0].m_obj;
lean_object* v_res_792_;
v_res_792_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v___y_757_);
stack->m_obj
 = v_res_792_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___boxed(lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v___y_793_);
lean_dec(v___y_793_);
return v_res_795_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v___y_807_);
return v___x_809_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_796_ = stack[0].m_obj;
lean_object* v___y_797_ = stack[1].m_obj;
lean_object* v___y_798_ = stack[2].m_obj;
lean_object* v___y_799_ = stack[3].m_obj;
lean_object* v___y_800_ = stack[4].m_obj;
lean_object* v___y_801_ = stack[5].m_obj;
lean_object* v___y_802_ = stack[6].m_obj;
lean_object* v___y_803_ = stack[7].m_obj;
lean_object* v___y_804_ = stack[8].m_obj;
lean_object* v___y_805_ = stack[9].m_obj;
lean_object* v___y_806_ = stack[10].m_obj;
lean_object* v___y_807_ = stack[11].m_obj;
lean_object* v_res_810_;
v_res_810_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
stack->m_obj
 = v_res_810_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___boxed(lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
return v_res_824_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(lean_object* v_opts_825_, lean_object* v_opt_826_){
_start:
{
lean_object* v_name_827_; lean_object* v_defValue_828_; lean_object* v_map_829_; lean_object* v___x_830_; 
v_name_827_ = lean_ctor_get(v_opt_826_, 0);
v_defValue_828_ = lean_ctor_get(v_opt_826_, 1);
v_map_829_ = lean_ctor_get(v_opts_825_, 0);
v___x_830_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_829_, v_name_827_);
if (lean_obj_tag(v___x_830_) == 0)
{
uint8_t v___x_831_; 
v___x_831_ = lean_unbox(v_defValue_828_);
return v___x_831_;
}
else
{
lean_object* v_val_832_; 
v_val_832_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_val_832_);
lean_dec_ref_known(v___x_830_, 1);
if (lean_obj_tag(v_val_832_) == 1)
{
uint8_t v_v_833_; 
v_v_833_ = lean_ctor_get_uint8(v_val_832_, 0);
lean_dec_ref_known(v_val_832_, 0);
return v_v_833_;
}
else
{
uint8_t v___x_834_; 
lean_dec(v_val_832_);
v___x_834_ = lean_unbox(v_defValue_828_);
return v___x_834_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_825_ = stack[0].m_obj;
lean_object* v_opt_826_ = stack[1].m_obj;
uint8_t v_res_835_;
v_res_835_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_opts_825_, v_opt_826_);
stack->m_num = v_res_835_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___boxed(lean_object* v_opts_836_, lean_object* v_opt_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_opts_836_, v_opt_837_);
lean_dec_ref(v_opt_837_);
lean_dec_ref(v_opts_836_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0(lean_object* v_x_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; 
lean_inc(v___y_848_);
lean_inc_ref(v___y_847_);
lean_inc(v___y_846_);
lean_inc_ref(v___y_845_);
lean_inc(v___y_844_);
lean_inc(v___y_843_);
lean_inc_ref(v___y_842_);
lean_inc(v___y_841_);
v___x_854_ = lean_apply_13(v_x_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, lean_box(0));
return v___x_854_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_840_ = stack[0].m_obj;
lean_object* v___y_841_ = stack[1].m_obj;
lean_object* v___y_842_ = stack[2].m_obj;
lean_object* v___y_843_ = stack[3].m_obj;
lean_object* v___y_844_ = stack[4].m_obj;
lean_object* v___y_845_ = stack[5].m_obj;
lean_object* v___y_846_ = stack[6].m_obj;
lean_object* v___y_847_ = stack[7].m_obj;
lean_object* v___y_848_ = stack[8].m_obj;
lean_object* v___y_849_ = stack[9].m_obj;
lean_object* v___y_850_ = stack[10].m_obj;
lean_object* v___y_851_ = stack[11].m_obj;
lean_object* v___y_852_ = stack[12].m_obj;
lean_object* v_res_855_;
v_res_855_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0(v_x_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
stack->m_obj
 = v_res_855_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0___boxed(lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0(v_x_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
return v_res_870_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(lean_object* v_mvarId_871_, lean_object* v_x_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___f_886_; lean_object* v___x_887_; 
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
lean_inc(v___y_876_);
lean_inc(v___y_875_);
lean_inc_ref(v___y_874_);
lean_inc(v___y_873_);
v___f_886_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_886_, 0, v_x_872_);
lean_closure_set(v___f_886_, 1, v___y_873_);
lean_closure_set(v___f_886_, 2, v___y_874_);
lean_closure_set(v___f_886_, 3, v___y_875_);
lean_closure_set(v___f_886_, 4, v___y_876_);
lean_closure_set(v___f_886_, 5, v___y_877_);
lean_closure_set(v___f_886_, 6, v___y_878_);
lean_closure_set(v___f_886_, 7, v___y_879_);
lean_closure_set(v___f_886_, 8, v___y_880_);
v___x_887_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_871_, v___f_886_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_887_) == 0)
{
return v___x_887_;
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_871_ = stack[0].m_obj;
lean_object* v_x_872_ = stack[1].m_obj;
lean_object* v___y_873_ = stack[2].m_obj;
lean_object* v___y_874_ = stack[3].m_obj;
lean_object* v___y_875_ = stack[4].m_obj;
lean_object* v___y_876_ = stack[5].m_obj;
lean_object* v___y_877_ = stack[6].m_obj;
lean_object* v___y_878_ = stack[7].m_obj;
lean_object* v___y_879_ = stack[8].m_obj;
lean_object* v___y_880_ = stack[9].m_obj;
lean_object* v___y_881_ = stack[10].m_obj;
lean_object* v___y_882_ = stack[11].m_obj;
lean_object* v___y_883_ = stack[12].m_obj;
lean_object* v___y_884_ = stack[13].m_obj;
lean_object* v_res_896_;
v_res_896_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(v_mvarId_871_, v_x_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
stack->m_obj
 = v_res_896_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___boxed(lean_object* v_mvarId_897_, lean_object* v_x_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(v_mvarId_897_, v_x_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
return v_res_912_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(lean_object* v_00_u03b1_913_, lean_object* v_mvarId_914_, lean_object* v_x_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(v_mvarId_914_, v_x_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
return v___x_929_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_914_ = stack[1].m_obj;
lean_object* v_x_915_ = stack[2].m_obj;
lean_object* v___y_916_ = stack[3].m_obj;
lean_object* v___y_917_ = stack[4].m_obj;
lean_object* v___y_918_ = stack[5].m_obj;
lean_object* v___y_919_ = stack[6].m_obj;
lean_object* v___y_920_ = stack[7].m_obj;
lean_object* v___y_921_ = stack[8].m_obj;
lean_object* v___y_922_ = stack[9].m_obj;
lean_object* v___y_923_ = stack[10].m_obj;
lean_object* v___y_924_ = stack[11].m_obj;
lean_object* v___y_925_ = stack[12].m_obj;
lean_object* v___y_926_ = stack[13].m_obj;
lean_object* v___y_927_ = stack[14].m_obj;
lean_object* v_res_930_;
v_res_930_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(lean_box(0), v_mvarId_914_, v_x_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
stack->m_obj
 = v_res_930_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___boxed(lean_object* v_00_u03b1_931_, lean_object* v_mvarId_932_, lean_object* v_x_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_00_u03b1_931_, v_mvarId_932_, v_x_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
return v_res_947_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1));
v___x_952_ = l_Lean_MessageData_ofFormat(v___x_951_);
return v___x_952_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(lean_object* v_x_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_953_ = stack[0].m_obj;
lean_object* v___y_954_ = stack[1].m_obj;
lean_object* v___y_955_ = stack[2].m_obj;
lean_object* v___y_956_ = stack[3].m_obj;
lean_object* v___y_957_ = stack[4].m_obj;
lean_object* v___y_958_ = stack[5].m_obj;
lean_object* v___y_959_ = stack[6].m_obj;
lean_object* v___y_960_ = stack[7].m_obj;
lean_object* v___y_961_ = stack[8].m_obj;
lean_object* v___y_962_ = stack[9].m_obj;
lean_object* v___y_963_ = stack[10].m_obj;
lean_object* v___y_964_ = stack[11].m_obj;
lean_object* v___y_965_ = stack[12].m_obj;
lean_object* v_res_969_;
v_res_969_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(v_x_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
stack->m_obj
 = v_res_969_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed(lean_object* v_x_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(v_x_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v_x_970_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7(lean_object* v_opts_985_, lean_object* v_opt_986_){
_start:
{
lean_object* v_name_987_; lean_object* v_defValue_988_; lean_object* v_map_989_; lean_object* v___x_990_; 
v_name_987_ = lean_ctor_get(v_opt_986_, 0);
v_defValue_988_ = lean_ctor_get(v_opt_986_, 1);
v_map_989_ = lean_ctor_get(v_opts_985_, 0);
v___x_990_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_989_, v_name_987_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_inc(v_defValue_988_);
return v_defValue_988_;
}
else
{
lean_object* v_val_991_; 
v_val_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v___x_990_, 1);
if (lean_obj_tag(v_val_991_) == 3)
{
lean_object* v_v_992_; 
v_v_992_ = lean_ctor_get(v_val_991_, 0);
lean_inc(v_v_992_);
lean_dec_ref_known(v_val_991_, 1);
return v_v_992_;
}
else
{
lean_dec(v_val_991_);
lean_inc(v_defValue_988_);
return v_defValue_988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7___boxed(lean_object* v_opts_993_, lean_object* v_opt_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7(v_opts_993_, v_opt_994_);
lean_dec_ref(v_opt_994_);
lean_dec_ref(v_opts_993_);
return v_res_995_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(lean_object* v_x_996_){
_start:
{
if (lean_obj_tag(v_x_996_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
v_a_998_ = lean_ctor_get(v_x_996_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v_x_996_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v_x_996_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set_tag(v___x_1000_, 1);
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
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_a_1006_ = lean_ctor_get(v_x_996_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v_x_996_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v_x_996_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set_tag(v___x_1008_, 0);
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_996_ = stack[0].m_obj;
lean_object* v_res_1014_;
v_res_1014_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(v_x_996_);
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg___boxed(lean_object* v_x_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(v_x_1015_);
return v_res_1017_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6(lean_object* v_e_1018_){
_start:
{
if (lean_obj_tag(v_e_1018_) == 0)
{
uint8_t v___x_1019_; 
v___x_1019_ = 2;
return v___x_1019_;
}
else
{
uint8_t v___x_1020_; 
v___x_1020_ = 0;
return v___x_1020_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1018_ = stack[0].m_obj;
uint8_t v_res_1021_;
v_res_1021_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6(v_e_1018_);
stack->m_num = v_res_1021_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6___boxed(lean_object* v_e_1022_){
_start:
{
uint8_t v_res_1023_; lean_object* v_r_1024_; 
v_res_1023_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6(v_e_1022_);
lean_dec_ref(v_e_1022_);
v_r_1024_ = lean_box(v_res_1023_);
return v_r_1024_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6(size_t v_sz_1025_, size_t v_i_1026_, lean_object* v_bs_1027_){
_start:
{
uint8_t v___x_1028_; 
v___x_1028_ = lean_usize_dec_lt(v_i_1026_, v_sz_1025_);
if (v___x_1028_ == 0)
{
return v_bs_1027_;
}
else
{
lean_object* v_v_1029_; lean_object* v_msg_1030_; lean_object* v___x_1031_; lean_object* v_bs_x27_1032_; size_t v___x_1033_; size_t v___x_1034_; lean_object* v___x_1035_; 
v_v_1029_ = lean_array_uget_borrowed(v_bs_1027_, v_i_1026_);
v_msg_1030_ = lean_ctor_get(v_v_1029_, 1);
lean_inc_ref(v_msg_1030_);
v___x_1031_ = lean_unsigned_to_nat(0u);
v_bs_x27_1032_ = lean_array_uset(v_bs_1027_, v_i_1026_, v___x_1031_);
v___x_1033_ = ((size_t)1ULL);
v___x_1034_ = lean_usize_add(v_i_1026_, v___x_1033_);
v___x_1035_ = lean_array_uset(v_bs_x27_1032_, v_i_1026_, v_msg_1030_);
v_i_1026_ = v___x_1034_;
v_bs_1027_ = v___x_1035_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1025_ = stack[0].m_num;
size_t v_i_1026_ = stack[1].m_num;
lean_object* v_bs_1027_ = stack[2].m_obj;
lean_object* v_res_1037_;
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6(v_sz_1025_, v_i_1026_, v_bs_1027_);
stack->m_obj
 = v_res_1037_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6___boxed(lean_object* v_sz_1038_, lean_object* v_i_1039_, lean_object* v_bs_1040_){
_start:
{
size_t v_sz_boxed_1041_; size_t v_i_boxed_1042_; lean_object* v_res_1043_; 
v_sz_boxed_1041_ = lean_unbox_usize(v_sz_1038_);
lean_dec(v_sz_1038_);
v_i_boxed_1042_ = lean_unbox_usize(v_i_1039_);
lean_dec(v_i_1039_);
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6(v_sz_boxed_1041_, v_i_boxed_1042_, v_bs_1040_);
return v_res_1043_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(lean_object* v_oldTraces_1044_, lean_object* v_data_1045_, lean_object* v_ref_1046_, lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_toCold_1053_; lean_object* v_currRecDepth_1054_; lean_object* v_ref_1055_; uint16_t v_optionFlags_1056_; uint8_t v_suppressElabErrors_1057_; uint8_t v_isRecordingDeps_1058_; lean_object* v_ref_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v_traceState_1062_; lean_object* v_traces_1063_; lean_object* v___x_1064_; size_t v_sz_1065_; size_t v___x_1066_; lean_object* v___x_1067_; lean_object* v_msg_1068_; lean_object* v___x_1069_; lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1108_; 
v_toCold_1053_ = lean_ctor_get(v___y_1050_, 0);
v_currRecDepth_1054_ = lean_ctor_get(v___y_1050_, 1);
v_ref_1055_ = lean_ctor_get(v___y_1050_, 2);
v_optionFlags_1056_ = lean_ctor_get_uint16(v___y_1050_, sizeof(void*)*3);
v_suppressElabErrors_1057_ = lean_ctor_get_uint8(v___y_1050_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1058_ = lean_ctor_get_uint8(v___y_1050_, sizeof(void*)*3 + 3);
v_ref_1059_ = l_Lean_replaceRef(v_ref_1046_, v_ref_1055_);
lean_inc(v_currRecDepth_1054_);
lean_inc_ref(v_toCold_1053_);
v___x_1060_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1060_, 0, v_toCold_1053_);
lean_ctor_set(v___x_1060_, 1, v_currRecDepth_1054_);
lean_ctor_set(v___x_1060_, 2, v_ref_1059_);
lean_ctor_set_uint16(v___x_1060_, sizeof(void*)*3, v_optionFlags_1056_);
lean_ctor_set_uint8(v___x_1060_, sizeof(void*)*3 + 2, v_suppressElabErrors_1057_);
lean_ctor_set_uint8(v___x_1060_, sizeof(void*)*3 + 3, v_isRecordingDeps_1058_);
v___x_1061_ = lean_st_ref_get(v___y_1051_);
v_traceState_1062_ = lean_ctor_get(v___x_1061_, 4);
lean_inc_ref(v_traceState_1062_);
lean_dec(v___x_1061_);
v_traces_1063_ = lean_ctor_get(v_traceState_1062_, 0);
lean_inc_ref(v_traces_1063_);
lean_dec_ref(v_traceState_1062_);
v___x_1064_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1063_);
lean_dec_ref(v_traces_1063_);
v_sz_1065_ = lean_array_size(v___x_1064_);
v___x_1066_ = ((size_t)0ULL);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6(v_sz_1065_, v___x_1066_, v___x_1064_);
v_msg_1068_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1068_, 0, v_data_1045_);
lean_ctor_set(v_msg_1068_, 1, v_msg_1047_);
lean_ctor_set(v_msg_1068_, 2, v___x_1067_);
v___x_1069_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_1068_, v___y_1048_, v___y_1049_, v___x_1060_, v___y_1051_);
lean_dec_ref_known(v___x_1060_, 3);
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1108_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1108_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v_traceState_1075_; lean_object* v_env_1076_; lean_object* v_nextMacroScope_1077_; lean_object* v_ngen_1078_; lean_object* v_auxDeclNGen_1079_; lean_object* v_cache_1080_; lean_object* v_recordedDeps_1081_; lean_object* v_messages_1082_; lean_object* v_infoState_1083_; lean_object* v_snapshotTasks_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1107_; 
v___x_1074_ = lean_st_ref_take(v___y_1051_);
v_traceState_1075_ = lean_ctor_get(v___x_1074_, 4);
v_env_1076_ = lean_ctor_get(v___x_1074_, 0);
v_nextMacroScope_1077_ = lean_ctor_get(v___x_1074_, 1);
v_ngen_1078_ = lean_ctor_get(v___x_1074_, 2);
v_auxDeclNGen_1079_ = lean_ctor_get(v___x_1074_, 3);
v_cache_1080_ = lean_ctor_get(v___x_1074_, 5);
v_recordedDeps_1081_ = lean_ctor_get(v___x_1074_, 6);
v_messages_1082_ = lean_ctor_get(v___x_1074_, 7);
v_infoState_1083_ = lean_ctor_get(v___x_1074_, 8);
v_snapshotTasks_1084_ = lean_ctor_get(v___x_1074_, 9);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1086_ = v___x_1074_;
v_isShared_1087_ = v_isSharedCheck_1107_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_snapshotTasks_1084_);
lean_inc(v_infoState_1083_);
lean_inc(v_messages_1082_);
lean_inc(v_recordedDeps_1081_);
lean_inc(v_cache_1080_);
lean_inc(v_traceState_1075_);
lean_inc(v_auxDeclNGen_1079_);
lean_inc(v_ngen_1078_);
lean_inc(v_nextMacroScope_1077_);
lean_inc(v_env_1076_);
lean_dec(v___x_1074_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1107_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
uint64_t v_tid_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1105_; 
v_tid_1088_ = lean_ctor_get_uint64(v_traceState_1075_, sizeof(void*)*1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_traceState_1075_);
if (v_isSharedCheck_1105_ == 0)
{
lean_object* v_unused_1106_; 
v_unused_1106_ = lean_ctor_get(v_traceState_1075_, 0);
lean_dec(v_unused_1106_);
v___x_1090_ = v_traceState_1075_;
v_isShared_1091_ = v_isSharedCheck_1105_;
goto v_resetjp_1089_;
}
else
{
lean_dec(v_traceState_1075_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1105_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_ref_1046_);
lean_ctor_set(v___x_1093_, 1, v_a_1070_);
v___x_1094_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1044_, v___x_1093_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1094_);
v___x_1096_ = v___x_1090_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1094_);
lean_ctor_set_uint64(v_reuseFailAlloc_1104_, sizeof(void*)*1, v_tid_1088_);
v___x_1096_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1098_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 4, v___x_1096_);
v___x_1098_ = v___x_1086_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_env_1076_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_nextMacroScope_1077_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_ngen_1078_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v_auxDeclNGen_1079_);
lean_ctor_set(v_reuseFailAlloc_1103_, 4, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1103_, 5, v_cache_1080_);
lean_ctor_set(v_reuseFailAlloc_1103_, 6, v_recordedDeps_1081_);
lean_ctor_set(v_reuseFailAlloc_1103_, 7, v_messages_1082_);
lean_ctor_set(v_reuseFailAlloc_1103_, 8, v_infoState_1083_);
lean_ctor_set(v_reuseFailAlloc_1103_, 9, v_snapshotTasks_1084_);
v___x_1098_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1099_ = lean_st_ref_put(v___y_1051_, v___x_1098_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1092_);
v___x_1101_ = v___x_1072_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1092_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_1044_ = stack[0].m_obj;
lean_object* v_data_1045_ = stack[1].m_obj;
lean_object* v_ref_1046_ = stack[2].m_obj;
lean_object* v_msg_1047_ = stack[3].m_obj;
lean_object* v___y_1048_ = stack[4].m_obj;
lean_object* v___y_1049_ = stack[5].m_obj;
lean_object* v___y_1050_ = stack[6].m_obj;
lean_object* v___y_1051_ = stack[7].m_obj;
lean_object* v_res_1109_;
v_res_1109_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(v_oldTraces_1044_, v_data_1045_, v_ref_1046_, v_msg_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
stack->m_obj
 = v_res_1109_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg___boxed(lean_object* v_oldTraces_1110_, lean_object* v_data_1111_, lean_object* v_ref_1112_, lean_object* v_msg_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(v_oldTraces_1110_, v_data_1111_, v_ref_1112_, v_msg_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1119_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1120_; double v___x_1121_; 
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_float_of_nat(v___x_1120_);
return v___x_1121_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__1));
v___x_1124_ = l_Lean_stringToMessageData(v___x_1123_);
return v___x_1124_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1125_; double v___x_1126_; 
v___x_1125_ = lean_unsigned_to_nat(1000u);
v___x_1126_ = lean_float_of_nat(v___x_1125_);
return v___x_1126_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(lean_object* v_cls_1127_, uint8_t v_collapsed_1128_, lean_object* v_tag_1129_, lean_object* v_opts_1130_, uint8_t v_clsEnabled_1131_, lean_object* v_oldTraces_1132_, lean_object* v_msg_1133_, lean_object* v_resStartStop_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_fst_1148_; lean_object* v_snd_1149_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v_data_1153_; lean_object* v_fst_1164_; lean_object* v_snd_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; lean_object* v___y_1169_; lean_object* v_a_1170_; uint8_t v___y_1185_; double v___y_1217_; 
v_fst_1148_ = lean_ctor_get(v_resStartStop_1134_, 0);
lean_inc(v_fst_1148_);
v_snd_1149_ = lean_ctor_get(v_resStartStop_1134_, 1);
lean_inc(v_snd_1149_);
lean_dec_ref(v_resStartStop_1134_);
v_fst_1164_ = lean_ctor_get(v_snd_1149_, 0);
lean_inc(v_fst_1164_);
v_snd_1165_ = lean_ctor_get(v_snd_1149_, 1);
lean_inc(v_snd_1165_);
lean_dec(v_snd_1149_);
v___x_1166_ = l_Lean_trace_profiler;
v___x_1167_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_opts_1130_, v___x_1166_);
if (v___x_1167_ == 0)
{
v___y_1185_ = v___x_1167_;
goto v___jp_1184_;
}
else
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1223_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_opts_1130_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; double v___x_1226_; double v___x_1227_; double v___x_1228_; 
v___x_1224_ = l_Lean_trace_profiler_threshold;
v___x_1225_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7(v_opts_1130_, v___x_1224_);
v___x_1226_ = lean_float_of_nat(v___x_1225_);
v___x_1227_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3);
v___x_1228_ = lean_float_div(v___x_1226_, v___x_1227_);
v___y_1217_ = v___x_1228_;
goto v___jp_1216_;
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; double v___x_1231_; 
v___x_1229_ = l_Lean_trace_profiler_threshold;
v___x_1230_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7(v_opts_1130_, v___x_1229_);
v___x_1231_ = lean_float_of_nat(v___x_1230_);
v___y_1217_ = v___x_1231_;
goto v___jp_1216_;
}
}
v___jp_1150_:
{
lean_object* v___x_1154_; 
lean_inc(v___y_1152_);
v___x_1154_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(v_oldTraces_1132_, v_data_1153_, v___y_1152_, v___y_1151_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v___x_1155_; 
lean_dec_ref_known(v___x_1154_, 1);
v___x_1155_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(v_fst_1148_);
return v___x_1155_;
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_fst_1148_);
v_a_1156_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1154_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1154_);
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
v___jp_1168_:
{
uint8_t v_result_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; double v___x_1174_; lean_object* v_data_1175_; 
v_result_1171_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6(v_fst_1148_);
v___x_1172_ = lean_box(v_result_1171_);
v___x_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
v___x_1174_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0);
lean_inc_ref(v_tag_1129_);
lean_inc_ref(v___x_1173_);
lean_inc(v_cls_1127_);
v_data_1175_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1175_, 0, v_cls_1127_);
lean_ctor_set(v_data_1175_, 1, v___x_1173_);
lean_ctor_set(v_data_1175_, 2, v_tag_1129_);
lean_ctor_set_float(v_data_1175_, sizeof(void*)*3, v___x_1174_);
lean_ctor_set_float(v_data_1175_, sizeof(void*)*3 + 8, v___x_1174_);
lean_ctor_set_uint8(v_data_1175_, sizeof(void*)*3 + 16, v_collapsed_1128_);
if (v___x_1167_ == 0)
{
lean_dec_ref_known(v___x_1173_, 1);
lean_dec(v_snd_1165_);
lean_dec(v_fst_1164_);
lean_dec_ref(v_tag_1129_);
lean_dec(v_cls_1127_);
v___y_1151_ = v_a_1170_;
v___y_1152_ = v___y_1169_;
v_data_1153_ = v_data_1175_;
goto v___jp_1150_;
}
else
{
lean_object* v_data_1176_; double v___x_1177_; double v___x_1178_; 
lean_dec_ref_known(v_data_1175_, 3);
v_data_1176_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1176_, 0, v_cls_1127_);
lean_ctor_set(v_data_1176_, 1, v___x_1173_);
lean_ctor_set(v_data_1176_, 2, v_tag_1129_);
v___x_1177_ = lean_unbox_float(v_fst_1164_);
lean_dec(v_fst_1164_);
lean_ctor_set_float(v_data_1176_, sizeof(void*)*3, v___x_1177_);
v___x_1178_ = lean_unbox_float(v_snd_1165_);
lean_dec(v_snd_1165_);
lean_ctor_set_float(v_data_1176_, sizeof(void*)*3 + 8, v___x_1178_);
lean_ctor_set_uint8(v_data_1176_, sizeof(void*)*3 + 16, v_collapsed_1128_);
v___y_1151_ = v_a_1170_;
v___y_1152_ = v___y_1169_;
v_data_1153_ = v_data_1176_;
goto v___jp_1150_;
}
}
v___jp_1179_:
{
lean_object* v_ref_1180_; lean_object* v___x_1181_; 
v_ref_1180_ = lean_ctor_get(v___y_1145_, 2);
lean_inc(v___y_1146_);
lean_inc_ref(v___y_1145_);
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
lean_inc(v___y_1140_);
lean_inc_ref(v___y_1139_);
lean_inc(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1135_);
lean_inc(v_fst_1148_);
v___x_1181_ = lean_apply_14(v_msg_1133_, v_fst_1148_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, lean_box(0));
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___y_1169_ = v_ref_1180_;
v_a_1170_ = v_a_1182_;
goto v___jp_1168_;
}
else
{
lean_object* v___x_1183_; 
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2);
v___y_1169_ = v_ref_1180_;
v_a_1170_ = v___x_1183_;
goto v___jp_1168_;
}
}
v___jp_1184_:
{
if (v_clsEnabled_1131_ == 0)
{
if (v___y_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v_traceState_1187_; lean_object* v_env_1188_; lean_object* v_nextMacroScope_1189_; lean_object* v_ngen_1190_; lean_object* v_auxDeclNGen_1191_; lean_object* v_cache_1192_; lean_object* v_recordedDeps_1193_; lean_object* v_messages_1194_; lean_object* v_infoState_1195_; lean_object* v_snapshotTasks_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1215_; 
lean_dec(v_snd_1165_);
lean_dec(v_fst_1164_);
lean_dec_ref(v_msg_1133_);
lean_dec_ref(v_tag_1129_);
lean_dec(v_cls_1127_);
v___x_1186_ = lean_st_ref_take(v___y_1146_);
v_traceState_1187_ = lean_ctor_get(v___x_1186_, 4);
v_env_1188_ = lean_ctor_get(v___x_1186_, 0);
v_nextMacroScope_1189_ = lean_ctor_get(v___x_1186_, 1);
v_ngen_1190_ = lean_ctor_get(v___x_1186_, 2);
v_auxDeclNGen_1191_ = lean_ctor_get(v___x_1186_, 3);
v_cache_1192_ = lean_ctor_get(v___x_1186_, 5);
v_recordedDeps_1193_ = lean_ctor_get(v___x_1186_, 6);
v_messages_1194_ = lean_ctor_get(v___x_1186_, 7);
v_infoState_1195_ = lean_ctor_get(v___x_1186_, 8);
v_snapshotTasks_1196_ = lean_ctor_get(v___x_1186_, 9);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1198_ = v___x_1186_;
v_isShared_1199_ = v_isSharedCheck_1215_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_snapshotTasks_1196_);
lean_inc(v_infoState_1195_);
lean_inc(v_messages_1194_);
lean_inc(v_recordedDeps_1193_);
lean_inc(v_cache_1192_);
lean_inc(v_traceState_1187_);
lean_inc(v_auxDeclNGen_1191_);
lean_inc(v_ngen_1190_);
lean_inc(v_nextMacroScope_1189_);
lean_inc(v_env_1188_);
lean_dec(v___x_1186_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1215_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
uint64_t v_tid_1200_; lean_object* v_traces_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1214_; 
v_tid_1200_ = lean_ctor_get_uint64(v_traceState_1187_, sizeof(void*)*1);
v_traces_1201_ = lean_ctor_get(v_traceState_1187_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_traceState_1187_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1203_ = v_traceState_1187_;
v_isShared_1204_ = v_isSharedCheck_1214_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_traces_1201_);
lean_dec(v_traceState_1187_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1214_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1132_, v_traces_1201_);
lean_dec_ref(v_traces_1201_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1205_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1205_);
lean_ctor_set_uint64(v_reuseFailAlloc_1213_, sizeof(void*)*1, v_tid_1200_);
v___x_1207_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1209_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 4, v___x_1207_);
v___x_1209_ = v___x_1198_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_env_1188_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_nextMacroScope_1189_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_ngen_1190_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_auxDeclNGen_1191_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1212_, 5, v_cache_1192_);
lean_ctor_set(v_reuseFailAlloc_1212_, 6, v_recordedDeps_1193_);
lean_ctor_set(v_reuseFailAlloc_1212_, 7, v_messages_1194_);
lean_ctor_set(v_reuseFailAlloc_1212_, 8, v_infoState_1195_);
lean_ctor_set(v_reuseFailAlloc_1212_, 9, v_snapshotTasks_1196_);
v___x_1209_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_st_ref_put(v___y_1146_, v___x_1209_);
v___x_1211_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(v_fst_1148_);
return v___x_1211_;
}
}
}
}
}
else
{
goto v___jp_1179_;
}
}
else
{
goto v___jp_1179_;
}
}
v___jp_1216_:
{
double v___x_1218_; double v___x_1219_; double v___x_1220_; uint8_t v___x_1221_; 
v___x_1218_ = lean_unbox_float(v_snd_1165_);
v___x_1219_ = lean_unbox_float(v_fst_1164_);
v___x_1220_ = lean_float_sub(v___x_1218_, v___x_1219_);
v___x_1221_ = lean_float_decLt(v___y_1217_, v___x_1220_);
v___y_1185_ = v___x_1221_;
goto v___jp_1184_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1127_ = stack[0].m_obj;
uint8_t v_collapsed_1128_ = stack[1].m_num;
lean_object* v_tag_1129_ = stack[2].m_obj;
lean_object* v_opts_1130_ = stack[3].m_obj;
uint8_t v_clsEnabled_1131_ = stack[4].m_num;
lean_object* v_oldTraces_1132_ = stack[5].m_obj;
lean_object* v_msg_1133_ = stack[6].m_obj;
lean_object* v_resStartStop_1134_ = stack[7].m_obj;
lean_object* v___y_1135_ = stack[8].m_obj;
lean_object* v___y_1136_ = stack[9].m_obj;
lean_object* v___y_1137_ = stack[10].m_obj;
lean_object* v___y_1138_ = stack[11].m_obj;
lean_object* v___y_1139_ = stack[12].m_obj;
lean_object* v___y_1140_ = stack[13].m_obj;
lean_object* v___y_1141_ = stack[14].m_obj;
lean_object* v___y_1142_ = stack[15].m_obj;
lean_object* v___y_1143_ = stack[16].m_obj;
lean_object* v___y_1144_ = stack[17].m_obj;
lean_object* v___y_1145_ = stack[18].m_obj;
lean_object* v___y_1146_ = stack[19].m_obj;
lean_object* v_res_1232_;
v_res_1232_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_cls_1127_, v_collapsed_1128_, v_tag_1129_, v_opts_1130_, v_clsEnabled_1131_, v_oldTraces_1132_, v_msg_1133_, v_resStartStop_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
stack->m_obj
 = v_res_1232_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___boxed(lean_object** _args){
lean_object* v_cls_1233_ = _args[0];
lean_object* v_collapsed_1234_ = _args[1];
lean_object* v_tag_1235_ = _args[2];
lean_object* v_opts_1236_ = _args[3];
lean_object* v_clsEnabled_1237_ = _args[4];
lean_object* v_oldTraces_1238_ = _args[5];
lean_object* v_msg_1239_ = _args[6];
lean_object* v_resStartStop_1240_ = _args[7];
lean_object* v___y_1241_ = _args[8];
lean_object* v___y_1242_ = _args[9];
lean_object* v___y_1243_ = _args[10];
lean_object* v___y_1244_ = _args[11];
lean_object* v___y_1245_ = _args[12];
lean_object* v___y_1246_ = _args[13];
lean_object* v___y_1247_ = _args[14];
lean_object* v___y_1248_ = _args[15];
lean_object* v___y_1249_ = _args[16];
lean_object* v___y_1250_ = _args[17];
lean_object* v___y_1251_ = _args[18];
lean_object* v___y_1252_ = _args[19];
lean_object* v___y_1253_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_1254_; uint8_t v_clsEnabled_boxed_1255_; lean_object* v_res_1256_; 
v_collapsed_boxed_1254_ = lean_unbox(v_collapsed_1234_);
v_clsEnabled_boxed_1255_ = lean_unbox(v_clsEnabled_1237_);
v_res_1256_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_cls_1233_, v_collapsed_boxed_1254_, v_tag_1235_, v_opts_1236_, v_clsEnabled_boxed_1255_, v_oldTraces_1238_, v_msg_1239_, v_resStartStop_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v_opts_1236_);
return v_res_1256_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(lean_object* v_cls_1260_, lean_object* v_msg_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_ref_1267_; lean_object* v___x_1268_; lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1314_; 
v_ref_1267_ = lean_ctor_get(v___y_1264_, 2);
v___x_1268_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1314_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1314_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v_traceState_1274_; lean_object* v_env_1275_; lean_object* v_nextMacroScope_1276_; lean_object* v_ngen_1277_; lean_object* v_auxDeclNGen_1278_; lean_object* v_cache_1279_; lean_object* v_recordedDeps_1280_; lean_object* v_messages_1281_; lean_object* v_infoState_1282_; lean_object* v_snapshotTasks_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1313_; 
v___x_1273_ = lean_st_ref_take(v___y_1265_);
v_traceState_1274_ = lean_ctor_get(v___x_1273_, 4);
v_env_1275_ = lean_ctor_get(v___x_1273_, 0);
v_nextMacroScope_1276_ = lean_ctor_get(v___x_1273_, 1);
v_ngen_1277_ = lean_ctor_get(v___x_1273_, 2);
v_auxDeclNGen_1278_ = lean_ctor_get(v___x_1273_, 3);
v_cache_1279_ = lean_ctor_get(v___x_1273_, 5);
v_recordedDeps_1280_ = lean_ctor_get(v___x_1273_, 6);
v_messages_1281_ = lean_ctor_get(v___x_1273_, 7);
v_infoState_1282_ = lean_ctor_get(v___x_1273_, 8);
v_snapshotTasks_1283_ = lean_ctor_get(v___x_1273_, 9);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1285_ = v___x_1273_;
v_isShared_1286_ = v_isSharedCheck_1313_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_snapshotTasks_1283_);
lean_inc(v_infoState_1282_);
lean_inc(v_messages_1281_);
lean_inc(v_recordedDeps_1280_);
lean_inc(v_cache_1279_);
lean_inc(v_traceState_1274_);
lean_inc(v_auxDeclNGen_1278_);
lean_inc(v_ngen_1277_);
lean_inc(v_nextMacroScope_1276_);
lean_inc(v_env_1275_);
lean_dec(v___x_1273_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1313_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
uint64_t v_tid_1287_; lean_object* v_traces_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1312_; 
v_tid_1287_ = lean_ctor_get_uint64(v_traceState_1274_, sizeof(void*)*1);
v_traces_1288_ = lean_ctor_get(v_traceState_1274_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_traceState_1274_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1290_ = v_traceState_1274_;
v_isShared_1291_ = v_isSharedCheck_1312_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_traces_1288_);
lean_dec(v_traceState_1274_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1312_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; double v___x_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1292_ = lean_box(0);
v___x_1293_ = lean_box(0);
v___x_1294_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0);
v___x_1295_ = 0;
v___x_1296_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__0));
v___x_1297_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1297_, 0, v_cls_1260_);
lean_ctor_set(v___x_1297_, 1, v___x_1293_);
lean_ctor_set(v___x_1297_, 2, v___x_1296_);
lean_ctor_set_float(v___x_1297_, sizeof(void*)*3, v___x_1294_);
lean_ctor_set_float(v___x_1297_, sizeof(void*)*3 + 8, v___x_1294_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*3 + 16, v___x_1295_);
v___x_1298_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__1));
v___x_1299_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1297_);
lean_ctor_set(v___x_1299_, 1, v_a_1269_);
lean_ctor_set(v___x_1299_, 2, v___x_1298_);
lean_inc(v_ref_1267_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v_ref_1267_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = l_Lean_PersistentArray_push___redArg(v_traces_1288_, v___x_1300_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1301_);
v___x_1303_ = v___x_1290_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1301_);
lean_ctor_set_uint64(v_reuseFailAlloc_1311_, sizeof(void*)*1, v_tid_1287_);
v___x_1303_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v___x_1303_);
v___x_1305_ = v___x_1285_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_env_1275_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_nextMacroScope_1276_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_ngen_1277_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_auxDeclNGen_1278_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1310_, 5, v_cache_1279_);
lean_ctor_set(v_reuseFailAlloc_1310_, 6, v_recordedDeps_1280_);
lean_ctor_set(v_reuseFailAlloc_1310_, 7, v_messages_1281_);
lean_ctor_set(v_reuseFailAlloc_1310_, 8, v_infoState_1282_);
lean_ctor_set(v_reuseFailAlloc_1310_, 9, v_snapshotTasks_1283_);
v___x_1305_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = lean_st_ref_put(v___y_1265_, v___x_1305_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1292_);
v___x_1308_ = v___x_1271_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1292_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1260_ = stack[0].m_obj;
lean_object* v_msg_1261_ = stack[1].m_obj;
lean_object* v___y_1262_ = stack[2].m_obj;
lean_object* v___y_1263_ = stack[3].m_obj;
lean_object* v___y_1264_ = stack[4].m_obj;
lean_object* v___y_1265_ = stack[5].m_obj;
lean_object* v_res_1315_;
v_res_1315_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(v_cls_1260_, v_msg_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
stack->m_obj
 = v_res_1315_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___boxed(lean_object* v_cls_1316_, lean_object* v_msg_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(v_cls_1316_, v_msg_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(lean_object* v_x_1331_){
_start:
{
switch(lean_obj_tag(v_x_1331_))
{
case 0:
{
lean_object* v_a_1332_; lean_object* v___x_1333_; 
v_a_1332_ = lean_ctor_get(v_x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v_x_1331_, 1);
v___x_1333_ = l_Std_Tactic_BVDecide_BVPred_toString(v_a_1332_);
return v___x_1333_;
}
case 1:
{
uint8_t v_a_1334_; 
v_a_1334_ = lean_ctor_get_uint8(v_x_1331_, 0);
lean_dec_ref_known(v_x_1331_, 0);
if (v_a_1334_ == 0)
{
lean_object* v___x_1335_; 
v___x_1335_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__0));
return v___x_1335_;
}
else
{
lean_object* v___x_1336_; 
v___x_1336_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__1));
return v___x_1336_;
}
}
case 2:
{
lean_object* v_a_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_a_1337_ = lean_ctor_get(v_x_1331_, 0);
lean_inc_ref(v_a_1337_);
lean_dec_ref_known(v_x_1331_, 1);
v___x_1338_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__2));
v___x_1339_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1337_);
v___x_1340_ = lean_string_append(v___x_1338_, v___x_1339_);
lean_dec_ref(v___x_1339_);
return v___x_1340_;
}
case 3:
{
uint8_t v_a_1341_; lean_object* v_a_1342_; lean_object* v_a_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_a_1341_ = lean_ctor_get_uint8(v_x_1331_, sizeof(void*)*2);
v_a_1342_ = lean_ctor_get(v_x_1331_, 0);
lean_inc_ref(v_a_1342_);
v_a_1343_ = lean_ctor_get(v_x_1331_, 1);
lean_inc_ref(v_a_1343_);
lean_dec_ref_known(v_x_1331_, 2);
v___x_1344_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__3));
v___x_1345_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1342_);
v___x_1346_ = lean_string_append(v___x_1344_, v___x_1345_);
lean_dec_ref(v___x_1345_);
v___x_1347_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__4));
v___x_1348_ = lean_string_append(v___x_1346_, v___x_1347_);
v___x_1349_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_1341_);
v___x_1350_ = lean_string_append(v___x_1348_, v___x_1349_);
lean_dec_ref(v___x_1349_);
v___x_1351_ = lean_string_append(v___x_1350_, v___x_1347_);
v___x_1352_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1343_);
v___x_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__5));
v___x_1355_ = lean_string_append(v___x_1353_, v___x_1354_);
return v___x_1355_;
}
default: 
{
lean_object* v_a_1356_; lean_object* v_a_1357_; lean_object* v_a_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v_a_1356_ = lean_ctor_get(v_x_1331_, 0);
lean_inc_ref(v_a_1356_);
v_a_1357_ = lean_ctor_get(v_x_1331_, 1);
lean_inc_ref(v_a_1357_);
v_a_1358_ = lean_ctor_get(v_x_1331_, 2);
lean_inc_ref(v_a_1358_);
lean_dec_ref_known(v_x_1331_, 3);
v___x_1359_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__6));
v___x_1360_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1356_);
v___x_1361_ = lean_string_append(v___x_1359_, v___x_1360_);
lean_dec_ref(v___x_1360_);
v___x_1362_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__4));
v___x_1363_ = lean_string_append(v___x_1361_, v___x_1362_);
v___x_1364_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1357_);
v___x_1365_ = lean_string_append(v___x_1363_, v___x_1364_);
lean_dec_ref(v___x_1364_);
v___x_1366_ = lean_string_append(v___x_1365_, v___x_1362_);
v___x_1367_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1358_);
v___x_1368_ = lean_string_append(v___x_1366_, v___x_1367_);
lean_dec_ref(v___x_1367_);
v___x_1369_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__5));
v___x_1370_ = lean_string_append(v___x_1368_, v___x_1369_);
return v___x_1370_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2));
v___x_1376_ = l_Lean_stringToMessageData(v___x_1375_);
return v___x_1376_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1377_; double v___x_1378_; 
v___x_1377_ = lean_unsigned_to_nat(1000000000u);
v___x_1378_ = lean_float_of_nat(v___x_1377_);
return v___x_1378_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(lean_object* v_unsatProver_1379_, lean_object* v_g_1380_, lean_object* v_cls_1381_, uint8_t v___x_1382_, lean_object* v___x_1383_, lean_object* v___f_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_toCold_1398_; lean_object* v_options_1399_; lean_object* v_inheritedTraceOptions_1400_; uint8_t v_hasTrace_1401_; lean_object* v___y_1403_; 
v_toCold_1398_ = lean_ctor_get(v___y_1395_, 0);
v_options_1399_ = lean_ctor_get(v_toCold_1398_, 2);
v_inheritedTraceOptions_1400_ = lean_ctor_get(v_toCold_1398_, 11);
v_hasTrace_1401_ = lean_ctor_get_uint8(v_options_1399_, sizeof(void*)*1);
if (v_hasTrace_1401_ == 0)
{
lean_object* v___x_1436_; 
lean_dec_ref(v___f_1384_);
lean_dec_ref(v___x_1383_);
lean_inc(v_g_1380_);
v___x_1436_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1380_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
v___y_1403_ = v___x_1436_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v_a_1443_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v_a_1458_; 
v___x_1437_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1));
lean_inc(v_cls_1381_);
v___x_1438_ = l_Lean_Name_append(v___x_1437_, v_cls_1381_);
v___x_1439_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1400_, v_options_1399_, v___x_1438_);
lean_dec(v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___x_1508_ = l_Lean_trace_profiler;
v___x_1509_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_options_1399_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
lean_dec_ref(v___f_1384_);
lean_dec_ref(v___x_1383_);
lean_inc(v_g_1380_);
v___x_1510_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1380_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
v___y_1403_ = v___x_1510_;
goto v___jp_1402_;
}
else
{
goto v___jp_1467_;
}
}
else
{
goto v___jp_1467_;
}
v___jp_1440_:
{
lean_object* v___x_1444_; double v___x_1445_; double v___x_1446_; double v___x_1447_; double v___x_1448_; double v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1444_ = lean_io_mono_nanos_now();
v___x_1445_ = lean_float_of_nat(v___y_1442_);
v___x_1446_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4);
v___x_1447_ = lean_float_div(v___x_1445_, v___x_1446_);
v___x_1448_ = lean_float_of_nat(v___x_1444_);
v___x_1449_ = lean_float_div(v___x_1448_, v___x_1446_);
v___x_1450_ = lean_box_float(v___x_1447_);
v___x_1451_ = lean_box_float(v___x_1449_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1453_, 0, v_a_1443_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
lean_inc(v_cls_1381_);
v___x_1454_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_cls_1381_, v___x_1382_, v___x_1383_, v_options_1399_, v___x_1439_, v___y_1441_, v___f_1384_, v___x_1453_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
v___y_1403_ = v___x_1454_;
goto v___jp_1402_;
}
v___jp_1455_:
{
lean_object* v___x_1459_; double v___x_1460_; double v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1459_ = lean_io_get_num_heartbeats();
v___x_1460_ = lean_float_of_nat(v___y_1457_);
v___x_1461_ = lean_float_of_nat(v___x_1459_);
v___x_1462_ = lean_box_float(v___x_1460_);
v___x_1463_ = lean_box_float(v___x_1461_);
v___x_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v_a_1458_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
lean_inc(v_cls_1381_);
v___x_1466_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_cls_1381_, v___x_1382_, v___x_1383_, v_options_1399_, v___x_1439_, v___y_1456_, v___f_1384_, v___x_1465_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
v___y_1403_ = v___x_1466_;
goto v___jp_1402_;
}
v___jp_1467_:
{
lean_object* v___x_1468_; lean_object* v_a_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1468_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v___y_1396_);
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref(v___x_1468_);
v___x_1470_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1471_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_options_1399_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_io_mono_nanos_now();
lean_inc(v_g_1380_);
v___x_1473_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1380_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
lean_ctor_set_tag(v___x_1476_, 1);
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
v___y_1441_ = v_a_1469_;
v___y_1442_ = v___x_1472_;
v_a_1443_ = v___x_1479_;
goto v___jp_1440_;
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
v_a_1482_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1473_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1473_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set_tag(v___x_1484_, 0);
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
v___y_1441_ = v_a_1469_;
v___y_1442_ = v___x_1472_;
v_a_1443_ = v___x_1487_;
goto v___jp_1440_;
}
}
}
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_io_get_num_heartbeats();
lean_inc(v_g_1380_);
v___x_1491_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1380_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set_tag(v___x_1494_, 1);
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
v___y_1456_ = v_a_1469_;
v___y_1457_ = v___x_1490_;
v_a_1458_ = v___x_1497_;
goto v___jp_1455_;
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
v_a_1500_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1491_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1491_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 0);
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
v___y_1456_ = v_a_1469_;
v___y_1457_ = v___x_1490_;
v_a_1458_ = v___x_1505_;
goto v___jp_1455_;
}
}
}
}
}
}
v___jp_1402_:
{
if (lean_obj_tag(v___y_1403_) == 0)
{
if (v_hasTrace_1401_ == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1405_; 
lean_dec(v_cls_1381_);
v_a_1404_ = lean_ctor_get(v___y_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___y_1403_, 1);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
lean_inc(v___y_1388_);
lean_inc(v___y_1387_);
lean_inc_ref(v___y_1386_);
lean_inc(v___y_1385_);
v___x_1405_ = lean_apply_15(v_unsatProver_1379_, v_g_1380_, v_a_1404_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, lean_box(0));
return v___x_1405_;
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v_a_1406_ = lean_ctor_get(v___y_1403_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___y_1403_, 1);
v___x_1407_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1));
lean_inc(v_cls_1381_);
v___x_1408_ = l_Lean_Name_append(v___x_1407_, v_cls_1381_);
v___x_1409_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1400_, v_options_1399_, v___x_1408_);
lean_dec(v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; 
lean_dec(v_cls_1381_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
lean_inc(v___y_1388_);
lean_inc(v___y_1387_);
lean_inc_ref(v___y_1386_);
lean_inc(v___y_1385_);
v___x_1410_ = lean_apply_15(v_unsatProver_1379_, v_g_1380_, v_a_1406_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, lean_box(0));
return v___x_1410_;
}
else
{
lean_object* v_satExpr_1411_; lean_object* v_bvExpr_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_satExpr_1411_ = lean_ctor_get(v_a_1406_, 0);
v_bvExpr_1412_ = lean_ctor_get(v_satExpr_1411_, 0);
v___x_1413_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3);
lean_inc_ref(v_bvExpr_1412_);
v___x_1414_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_bvExpr_1412_);
v___x_1415_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
v___x_1416_ = l_Lean_MessageData_ofFormat(v___x_1415_);
v___x_1417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1413_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(v_cls_1381_, v___x_1417_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1419_; 
lean_dec_ref_known(v___x_1418_, 1);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
lean_inc(v___y_1388_);
lean_inc(v___y_1387_);
lean_inc_ref(v___y_1386_);
lean_inc(v___y_1385_);
v___x_1419_ = lean_apply_15(v_unsatProver_1379_, v_g_1380_, v_a_1406_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, lean_box(0));
return v___x_1419_;
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec(v_a_1406_);
lean_dec(v_g_1380_);
lean_dec_ref(v_unsatProver_1379_);
v_a_1420_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1418_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1418_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v_cls_1381_);
lean_dec(v_g_1380_);
lean_dec_ref(v_unsatProver_1379_);
v_a_1428_ = lean_ctor_get(v___y_1403_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___y_1403_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___y_1403_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___y_1403_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_unsatProver_1379_ = stack[0].m_obj;
lean_object* v_g_1380_ = stack[1].m_obj;
lean_object* v_cls_1381_ = stack[2].m_obj;
uint8_t v___x_1382_ = stack[3].m_num;
lean_object* v___x_1383_ = stack[4].m_obj;
lean_object* v___f_1384_ = stack[5].m_obj;
lean_object* v___y_1385_ = stack[6].m_obj;
lean_object* v___y_1386_ = stack[7].m_obj;
lean_object* v___y_1387_ = stack[8].m_obj;
lean_object* v___y_1388_ = stack[9].m_obj;
lean_object* v___y_1389_ = stack[10].m_obj;
lean_object* v___y_1390_ = stack[11].m_obj;
lean_object* v___y_1391_ = stack[12].m_obj;
lean_object* v___y_1392_ = stack[13].m_obj;
lean_object* v___y_1393_ = stack[14].m_obj;
lean_object* v___y_1394_ = stack[15].m_obj;
lean_object* v___y_1395_ = stack[16].m_obj;
lean_object* v___y_1396_ = stack[17].m_obj;
lean_object* v_res_1511_;
v_res_1511_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(v_unsatProver_1379_, v_g_1380_, v_cls_1381_, v___x_1382_, v___x_1383_, v___f_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
stack->m_obj
 = v_res_1511_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_unsatProver_1512_ = _args[0];
lean_object* v_g_1513_ = _args[1];
lean_object* v_cls_1514_ = _args[2];
lean_object* v___x_1515_ = _args[3];
lean_object* v___x_1516_ = _args[4];
lean_object* v___f_1517_ = _args[5];
lean_object* v___y_1518_ = _args[6];
lean_object* v___y_1519_ = _args[7];
lean_object* v___y_1520_ = _args[8];
lean_object* v___y_1521_ = _args[9];
lean_object* v___y_1522_ = _args[10];
lean_object* v___y_1523_ = _args[11];
lean_object* v___y_1524_ = _args[12];
lean_object* v___y_1525_ = _args[13];
lean_object* v___y_1526_ = _args[14];
lean_object* v___y_1527_ = _args[15];
lean_object* v___y_1528_ = _args[16];
lean_object* v___y_1529_ = _args[17];
lean_object* v___y_1530_ = _args[18];
_start:
{
uint8_t v___x_64978__boxed_1531_; lean_object* v_res_1532_; 
v___x_64978__boxed_1531_ = lean_unbox(v___x_1515_);
v_res_1532_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(v_unsatProver_1512_, v_g_1513_, v_cls_1514_, v___x_64978__boxed_1531_, v___x_1516_, v___f_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
return v_res_1532_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(lean_object* v_g_1541_, lean_object* v_unsatProver_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v___f_1555_; lean_object* v_cls_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___f_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___f_1555_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0));
v_cls_1556_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4));
v___x_1557_ = 1;
v___x_1558_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__0));
v___x_1559_ = lean_box(v___x_1557_);
lean_inc(v_g_1541_);
v___f_1560_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed), 19, 6);
lean_closure_set(v___f_1560_, 0, v_unsatProver_1542_);
lean_closure_set(v___f_1560_, 1, v_g_1541_);
lean_closure_set(v___f_1560_, 2, v_cls_1556_);
lean_closure_set(v___f_1560_, 3, v___x_1559_);
lean_closure_set(v___f_1560_, 4, v___x_1558_);
lean_closure_set(v___f_1560_, 5, v___f_1555_);
v___x_1561_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___boxed), 16, 3);
lean_closure_set(v___x_1561_, 0, lean_box(0));
lean_closure_set(v___x_1561_, 1, v_g_1541_);
lean_closure_set(v___x_1561_, 2, v___f_1560_);
v___x_1562_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4);
v___x_1563_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v___x_1561_, v___x_1562_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1572_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v_fst_1568_; lean_object* v___x_1570_; 
v_fst_1568_ = lean_ctor_get(v_a_1564_, 0);
lean_inc(v_fst_1568_);
lean_dec(v_a_1564_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v_fst_1568_);
v___x_1570_ = v___x_1566_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_fst_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
v_a_1573_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1563_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1563_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_1541_ = stack[0].m_obj;
lean_object* v_unsatProver_1542_ = stack[1].m_obj;
lean_object* v_a_1543_ = stack[2].m_obj;
lean_object* v_a_1544_ = stack[3].m_obj;
lean_object* v_a_1545_ = stack[4].m_obj;
lean_object* v_a_1546_ = stack[5].m_obj;
lean_object* v_a_1547_ = stack[6].m_obj;
lean_object* v_a_1548_ = stack[7].m_obj;
lean_object* v_a_1549_ = stack[8].m_obj;
lean_object* v_a_1550_ = stack[9].m_obj;
lean_object* v_a_1551_ = stack[10].m_obj;
lean_object* v_a_1552_ = stack[11].m_obj;
lean_object* v_a_1553_ = stack[12].m_obj;
lean_object* v_res_1581_;
v_res_1581_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1541_, v_unsatProver_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
stack->m_obj
 = v_res_1581_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___boxed(lean_object* v_g_1582_, lean_object* v_unsatProver_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1582_, v_unsatProver_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec_ref(v_a_1587_);
lean_dec(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
return v_res_1596_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(lean_object* v_00_u03b1_1597_, lean_object* v_g_1598_, lean_object* v_unsatProver_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1598_, v_unsatProver_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
return v___x_1612_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_1598_ = stack[1].m_obj;
lean_object* v_unsatProver_1599_ = stack[2].m_obj;
lean_object* v_a_1600_ = stack[3].m_obj;
lean_object* v_a_1601_ = stack[4].m_obj;
lean_object* v_a_1602_ = stack[5].m_obj;
lean_object* v_a_1603_ = stack[6].m_obj;
lean_object* v_a_1604_ = stack[7].m_obj;
lean_object* v_a_1605_ = stack[8].m_obj;
lean_object* v_a_1606_ = stack[9].m_obj;
lean_object* v_a_1607_ = stack[10].m_obj;
lean_object* v_a_1608_ = stack[11].m_obj;
lean_object* v_a_1609_ = stack[12].m_obj;
lean_object* v_a_1610_ = stack[13].m_obj;
lean_object* v_res_1613_;
v_res_1613_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(lean_box(0), v_g_1598_, v_unsatProver_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
stack->m_obj
 = v_res_1613_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed(lean_object* v_00_u03b1_1614_, lean_object* v_g_1615_, lean_object* v_unsatProver_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(v_00_u03b1_1614_, v_g_1615_, v_unsatProver_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
return v_res_1629_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(lean_object* v_cls_1630_, lean_object* v_msg_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(v_cls_1630_, v_msg_1631_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1630_ = stack[0].m_obj;
lean_object* v_msg_1631_ = stack[1].m_obj;
lean_object* v___y_1632_ = stack[2].m_obj;
lean_object* v___y_1633_ = stack[3].m_obj;
lean_object* v___y_1634_ = stack[4].m_obj;
lean_object* v___y_1635_ = stack[5].m_obj;
lean_object* v___y_1636_ = stack[6].m_obj;
lean_object* v___y_1637_ = stack[7].m_obj;
lean_object* v___y_1638_ = stack[8].m_obj;
lean_object* v___y_1639_ = stack[9].m_obj;
lean_object* v___y_1640_ = stack[10].m_obj;
lean_object* v___y_1641_ = stack[11].m_obj;
lean_object* v___y_1642_ = stack[12].m_obj;
lean_object* v___y_1643_ = stack[13].m_obj;
lean_object* v_res_1646_;
v_res_1646_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(v_cls_1630_, v_msg_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
stack->m_obj
 = v_res_1646_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___boxed(lean_object* v_cls_1647_, lean_object* v_msg_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(v_cls_1647_, v_msg_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
return v_res_1662_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5(lean_object* v_00_u03b1_1663_, lean_object* v_x_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(v_x_1664_);
return v___x_1678_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1664_ = stack[1].m_obj;
lean_object* v___y_1665_ = stack[2].m_obj;
lean_object* v___y_1666_ = stack[3].m_obj;
lean_object* v___y_1667_ = stack[4].m_obj;
lean_object* v___y_1668_ = stack[5].m_obj;
lean_object* v___y_1669_ = stack[6].m_obj;
lean_object* v___y_1670_ = stack[7].m_obj;
lean_object* v___y_1671_ = stack[8].m_obj;
lean_object* v___y_1672_ = stack[9].m_obj;
lean_object* v___y_1673_ = stack[10].m_obj;
lean_object* v___y_1674_ = stack[11].m_obj;
lean_object* v___y_1675_ = stack[12].m_obj;
lean_object* v___y_1676_ = stack[13].m_obj;
lean_object* v_res_1679_;
v_res_1679_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5(lean_box(0), v_x_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
stack->m_obj
 = v_res_1679_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1680_, lean_object* v_x_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5(v_00_u03b1_1680_, v_x_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
return v_res_1695_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4(lean_object* v_oldTraces_1696_, lean_object* v_data_1697_, lean_object* v_ref_1698_, lean_object* v_msg_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(v_oldTraces_1696_, v_data_1697_, v_ref_1698_, v_msg_1699_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_1696_ = stack[0].m_obj;
lean_object* v_data_1697_ = stack[1].m_obj;
lean_object* v_ref_1698_ = stack[2].m_obj;
lean_object* v_msg_1699_ = stack[3].m_obj;
lean_object* v___y_1700_ = stack[4].m_obj;
lean_object* v___y_1701_ = stack[5].m_obj;
lean_object* v___y_1702_ = stack[6].m_obj;
lean_object* v___y_1703_ = stack[7].m_obj;
lean_object* v___y_1704_ = stack[8].m_obj;
lean_object* v___y_1705_ = stack[9].m_obj;
lean_object* v___y_1706_ = stack[10].m_obj;
lean_object* v___y_1707_ = stack[11].m_obj;
lean_object* v___y_1708_ = stack[12].m_obj;
lean_object* v___y_1709_ = stack[13].m_obj;
lean_object* v___y_1710_ = stack[14].m_obj;
lean_object* v___y_1711_ = stack[15].m_obj;
lean_object* v_res_1714_;
v_res_1714_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4(v_oldTraces_1696_, v_data_1697_, v_ref_1698_, v_msg_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
stack->m_obj
 = v_res_1714_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___boxed(lean_object** _args){
lean_object* v_oldTraces_1715_ = _args[0];
lean_object* v_data_1716_ = _args[1];
lean_object* v_ref_1717_ = _args[2];
lean_object* v_msg_1718_ = _args[3];
lean_object* v___y_1719_ = _args[4];
lean_object* v___y_1720_ = _args[5];
lean_object* v___y_1721_ = _args[6];
lean_object* v___y_1722_ = _args[7];
lean_object* v___y_1723_ = _args[8];
lean_object* v___y_1724_ = _args[9];
lean_object* v___y_1725_ = _args[10];
lean_object* v___y_1726_ = _args[11];
lean_object* v___y_1727_ = _args[12];
lean_object* v___y_1728_ = _args[13];
lean_object* v___y_1729_ = _args[14];
lean_object* v___y_1730_ = _args[15];
lean_object* v___y_1731_ = _args[16];
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4(v_oldTraces_1715_, v_data_1716_, v_ref_1717_, v_msg_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
return v_res_1732_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Counterexample(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Counterexample(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Counterexample(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Counterexample(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
