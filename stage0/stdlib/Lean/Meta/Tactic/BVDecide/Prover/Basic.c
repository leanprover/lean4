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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(lean_object* v_f_1_, lean_object* v_x_2_, lean_object* v_g_3_, lean_object* v_r_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg___boxed(lean_object** _args){
lean_object* v_f_55_ = _args[0];
lean_object* v_x_56_ = _args[1];
lean_object* v_g_57_ = _args[2];
lean_object* v_r_58_ = _args[3];
lean_object* v_a_59_ = _args[4];
lean_object* v_a_60_ = _args[5];
lean_object* v_a_61_ = _args[6];
lean_object* v_a_62_ = _args[7];
lean_object* v_a_63_ = _args[8];
lean_object* v_a_64_ = _args[9];
lean_object* v_a_65_ = _args[10];
lean_object* v_a_66_ = _args[11];
lean_object* v_a_67_ = _args[12];
lean_object* v_a_68_ = _args[13];
lean_object* v_a_69_ = _args[14];
lean_object* v_a_70_ = _args[15];
lean_object* v_a_71_ = _args[16];
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(v_f_55_, v_x_56_, v_g_57_, v_r_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map(lean_object* v_00_u03b1_73_, lean_object* v_00_u03b2_74_, lean_object* v_f_75_, lean_object* v_x_76_, lean_object* v_g_77_, lean_object* v_r_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(v_f_75_, v_x_76_, v_g_77_, v_r_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___boxed(lean_object** _args){
lean_object* v_00_u03b1_93_ = _args[0];
lean_object* v_00_u03b2_94_ = _args[1];
lean_object* v_f_95_ = _args[2];
lean_object* v_x_96_ = _args[3];
lean_object* v_g_97_ = _args[4];
lean_object* v_r_98_ = _args[5];
lean_object* v_a_99_ = _args[6];
lean_object* v_a_100_ = _args[7];
lean_object* v_a_101_ = _args[8];
lean_object* v_a_102_ = _args[9];
lean_object* v_a_103_ = _args[10];
lean_object* v_a_104_ = _args[11];
lean_object* v_a_105_ = _args[12];
lean_object* v_a_106_ = _args[13];
lean_object* v_a_107_ = _args[14];
lean_object* v_a_108_ = _args[15];
lean_object* v_a_109_ = _args[16];
lean_object* v_a_110_ = _args[17];
lean_object* v_a_111_ = _args[18];
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Meta_Tactic_BVDecide_UnsatProver_map(v_00_u03b1_93_, v_00_u03b2_94_, v_f_95_, v_x_96_, v_g_97_, v_r_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0(lean_object* v_x_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; 
lean_inc(v___y_120_);
lean_inc_ref(v___y_119_);
lean_inc(v___y_118_);
lean_inc_ref(v___y_117_);
lean_inc(v___y_116_);
lean_inc(v___y_115_);
lean_inc_ref(v___y_114_);
v___x_126_ = lean_apply_12(v_x_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, lean_box(0));
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0___boxed(lean_object* v_x_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0(v_x_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(lean_object* v_mvarId_141_, lean_object* v_x_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___f_155_; lean_object* v___x_156_; 
lean_inc(v___y_149_);
lean_inc_ref(v___y_148_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v___y_145_);
lean_inc(v___y_144_);
lean_inc_ref(v___y_143_);
v___f_155_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_155_, 0, v_x_142_);
lean_closure_set(v___f_155_, 1, v___y_143_);
lean_closure_set(v___f_155_, 2, v___y_144_);
lean_closure_set(v___f_155_, 3, v___y_145_);
lean_closure_set(v___f_155_, 4, v___y_146_);
lean_closure_set(v___f_155_, 5, v___y_147_);
lean_closure_set(v___f_155_, 6, v___y_148_);
lean_closure_set(v___f_155_, 7, v___y_149_);
v___x_156_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_141_, v___f_155_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
if (lean_obj_tag(v___x_156_) == 0)
{
return v___x_156_;
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___boxed(lean_object* v_mvarId_165_, lean_object* v_x_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_mvarId_165_, v_x_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(lean_object* v_00_u03b1_180_, lean_object* v_mvarId_181_, lean_object* v_x_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_mvarId_181_, v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___boxed(lean_object* v_00_u03b1_196_, lean_object* v_mvarId_197_, lean_object* v_x_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(v_00_u03b1_196_, v_mvarId_197_, v_x_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(lean_object* v_msgData_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; lean_object* v_env_219_; uint8_t v___x_220_; lean_object* v_env_221_; lean_object* v___x_222_; lean_object* v_toCold_223_; lean_object* v_mctx_224_; lean_object* v_lctx_225_; lean_object* v_options_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_218_ = lean_st_ref_get(v___y_216_);
v_env_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc_ref(v_env_219_);
lean_dec(v___x_218_);
v___x_220_ = 0;
v_env_221_ = l_Lean_Environment_setRecordingDeps(v_env_219_, v___x_220_);
v___x_222_ = lean_st_ref_get(v___y_214_);
v_toCold_223_ = lean_ctor_get(v___y_215_, 0);
v_mctx_224_ = lean_ctor_get(v___x_222_, 0);
lean_inc_ref(v_mctx_224_);
lean_dec(v___x_222_);
v_lctx_225_ = lean_ctor_get(v___y_213_, 2);
v_options_226_ = lean_ctor_get(v_toCold_223_, 2);
lean_inc_ref(v_options_226_);
lean_inc_ref(v_lctx_225_);
v___x_227_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_227_, 0, v_env_221_);
lean_ctor_set(v___x_227_, 1, v_mctx_224_);
lean_ctor_set(v___x_227_, 2, v_lctx_225_);
lean_ctor_set(v___x_227_, 3, v_options_226_);
v___x_228_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v_msgData_212_);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5___boxed(lean_object* v_msgData_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msgData_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(lean_object* v_msg_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_ref_243_; lean_object* v___x_244_; lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_253_; 
v_ref_243_ = lean_ctor_get(v___y_240_, 2);
v___x_244_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_253_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_253_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_251_; 
lean_inc(v_ref_243_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v_ref_243_);
lean_ctor_set(v___x_249_, 1, v_a_245_);
if (v_isShared_248_ == 0)
{
lean_ctor_set_tag(v___x_247_, 1);
lean_ctor_set(v___x_247_, 0, v___x_249_);
v___x_251_ = v___x_247_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg___boxed(lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
return v_res_260_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(lean_object* v_a_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
uint8_t v___x_263_; 
v___x_263_ = 0;
return v___x_263_;
}
else
{
lean_object* v_key_264_; lean_object* v_tail_265_; lean_object* v_type_266_; lean_object* v_type_267_; uint8_t v___x_268_; 
v_key_264_ = lean_ctor_get(v_x_262_, 0);
v_tail_265_ = lean_ctor_get(v_x_262_, 2);
v_type_266_ = lean_ctor_get(v_key_264_, 1);
v_type_267_ = lean_ctor_get(v_a_261_, 1);
v___x_268_ = lean_expr_eqv(v_type_266_, v_type_267_);
if (v___x_268_ == 0)
{
v_x_262_ = v_tail_265_;
goto _start;
}
else
{
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg___boxed(lean_object* v_a_270_, lean_object* v_x_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_270_, v_x_271_);
lean_dec(v_x_271_);
lean_dec_ref(v_a_270_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
return v_x_274_;
}
else
{
lean_object* v_key_276_; lean_object* v_value_277_; lean_object* v_tail_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_302_; 
v_key_276_ = lean_ctor_get(v_x_275_, 0);
v_value_277_ = lean_ctor_get(v_x_275_, 1);
v_tail_278_ = lean_ctor_get(v_x_275_, 2);
v_isSharedCheck_302_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_302_ == 0)
{
v___x_280_ = v_x_275_;
v_isShared_281_ = v_isSharedCheck_302_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_tail_278_);
lean_inc(v_value_277_);
lean_inc(v_key_276_);
lean_dec(v_x_275_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_302_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v_type_282_; lean_object* v___x_283_; uint64_t v___x_284_; uint64_t v___x_285_; uint64_t v___x_286_; uint64_t v_fold_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; size_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v_type_282_ = lean_ctor_get(v_key_276_, 1);
v___x_283_ = lean_array_get_size(v_x_274_);
v___x_284_ = l_Lean_Expr_hash(v_type_282_);
v___x_285_ = 32ULL;
v___x_286_ = lean_uint64_shift_right(v___x_284_, v___x_285_);
v_fold_287_ = lean_uint64_xor(v___x_284_, v___x_286_);
v___x_288_ = 16ULL;
v___x_289_ = lean_uint64_shift_right(v_fold_287_, v___x_288_);
v___x_290_ = lean_uint64_xor(v_fold_287_, v___x_289_);
v___x_291_ = lean_uint64_to_usize(v___x_290_);
v___x_292_ = lean_usize_of_nat(v___x_283_);
v___x_293_ = ((size_t)1ULL);
v___x_294_ = lean_usize_sub(v___x_292_, v___x_293_);
v___x_295_ = lean_usize_land(v___x_291_, v___x_294_);
v___x_296_ = lean_array_uget_borrowed(v_x_274_, v___x_295_);
lean_inc(v___x_296_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 2, v___x_296_);
v___x_298_ = v___x_280_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_key_276_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_value_277_);
lean_ctor_set(v_reuseFailAlloc_301_, 2, v___x_296_);
v___x_298_ = v_reuseFailAlloc_301_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; 
v___x_299_ = lean_array_uset(v_x_274_, v___x_295_, v___x_298_);
v_x_274_ = v___x_299_;
v_x_275_ = v_tail_278_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(lean_object* v_i_303_, lean_object* v_source_304_, lean_object* v_target_305_){
_start:
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = lean_array_get_size(v_source_304_);
v___x_307_ = lean_nat_dec_lt(v_i_303_, v___x_306_);
if (v___x_307_ == 0)
{
lean_dec_ref(v_source_304_);
lean_dec(v_i_303_);
return v_target_305_;
}
else
{
lean_object* v_es_308_; lean_object* v___x_309_; lean_object* v_source_310_; lean_object* v_target_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_es_308_ = lean_array_fget(v_source_304_, v_i_303_);
v___x_309_ = lean_box(0);
v_source_310_ = lean_array_fset(v_source_304_, v_i_303_, v___x_309_);
v_target_311_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(v_target_305_, v_es_308_);
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_add(v_i_303_, v___x_312_);
lean_dec(v_i_303_);
v_i_303_ = v___x_313_;
v_source_304_ = v_source_310_;
v_target_305_ = v_target_311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(lean_object* v_data_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v_nbuckets_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_316_ = lean_array_get_size(v_data_315_);
v___x_317_ = lean_unsigned_to_nat(2u);
v_nbuckets_318_ = lean_nat_mul(v___x_316_, v___x_317_);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_box(0);
v___x_321_ = lean_mk_array(v_nbuckets_318_, v___x_320_);
v___x_322_ = lean_array_propagate_mark(v_data_315_, v___x_321_);
v___x_323_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v___x_319_, v_data_315_, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(lean_object* v_m_324_, lean_object* v_a_325_, lean_object* v_b_326_){
_start:
{
lean_object* v_size_327_; lean_object* v_buckets_328_; lean_object* v_type_329_; lean_object* v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v_fold_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; lean_object* v_bkt_343_; uint8_t v___x_344_; 
v_size_327_ = lean_ctor_get(v_m_324_, 0);
v_buckets_328_ = lean_ctor_get(v_m_324_, 1);
v_type_329_ = lean_ctor_get(v_a_325_, 1);
v___x_330_ = lean_array_get_size(v_buckets_328_);
v___x_331_ = l_Lean_Expr_hash(v_type_329_);
v___x_332_ = 32ULL;
v___x_333_ = lean_uint64_shift_right(v___x_331_, v___x_332_);
v_fold_334_ = lean_uint64_xor(v___x_331_, v___x_333_);
v___x_335_ = 16ULL;
v___x_336_ = lean_uint64_shift_right(v_fold_334_, v___x_335_);
v___x_337_ = lean_uint64_xor(v_fold_334_, v___x_336_);
v___x_338_ = lean_uint64_to_usize(v___x_337_);
v___x_339_ = lean_usize_of_nat(v___x_330_);
v___x_340_ = ((size_t)1ULL);
v___x_341_ = lean_usize_sub(v___x_339_, v___x_340_);
v___x_342_ = lean_usize_land(v___x_338_, v___x_341_);
v_bkt_343_ = lean_array_uget_borrowed(v_buckets_328_, v___x_342_);
v___x_344_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_325_, v_bkt_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_365_; 
lean_inc_ref(v_buckets_328_);
lean_inc(v_size_327_);
v_isSharedCheck_365_ = !lean_is_exclusive(v_m_324_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; lean_object* v_unused_367_; 
v_unused_366_ = lean_ctor_get(v_m_324_, 1);
lean_dec(v_unused_366_);
v_unused_367_ = lean_ctor_get(v_m_324_, 0);
lean_dec(v_unused_367_);
v___x_346_ = v_m_324_;
v_isShared_347_ = v_isSharedCheck_365_;
goto v_resetjp_345_;
}
else
{
lean_dec(v_m_324_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_365_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v_size_x27_349_; lean_object* v___x_350_; lean_object* v_buckets_x27_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_348_ = lean_unsigned_to_nat(1u);
v_size_x27_349_ = lean_nat_add(v_size_327_, v___x_348_);
lean_dec(v_size_327_);
lean_inc(v_bkt_343_);
v___x_350_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_350_, 0, v_a_325_);
lean_ctor_set(v___x_350_, 1, v_b_326_);
lean_ctor_set(v___x_350_, 2, v_bkt_343_);
v_buckets_x27_351_ = lean_array_uset(v_buckets_328_, v___x_342_, v___x_350_);
v___x_352_ = lean_unsigned_to_nat(4u);
v___x_353_ = lean_nat_mul(v_size_x27_349_, v___x_352_);
v___x_354_ = lean_unsigned_to_nat(3u);
v___x_355_ = lean_nat_div(v___x_353_, v___x_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_array_get_size(v_buckets_x27_351_);
v___x_357_ = lean_nat_dec_le(v___x_355_, v___x_356_);
lean_dec(v___x_355_);
if (v___x_357_ == 0)
{
lean_object* v_val_358_; lean_object* v___x_360_; 
v_val_358_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_buckets_x27_351_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v_val_358_);
lean_ctor_set(v___x_346_, 0, v_size_x27_349_);
v___x_360_ = v___x_346_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_size_x27_349_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_val_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
else
{
lean_object* v___x_363_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v_buckets_x27_351_);
lean_ctor_set(v___x_346_, 0, v_size_x27_349_);
v___x_363_ = v___x_346_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_size_x27_349_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_buckets_x27_351_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
else
{
lean_dec(v_b_326_);
lean_dec_ref(v_a_325_);
return v_m_324_;
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_box(0);
v___x_372_ = lean_unsigned_to_nat(16u);
v___x_373_ = lean_mk_array(v___x_372_, v___x_371_);
return v___x_373_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2);
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4(void){
_start:
{
lean_object* v___x_377_; lean_object* v_sats_378_; lean_object* v___x_379_; 
v___x_377_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3);
v_sats_378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0));
v___x_379_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_379_, 0, v_sats_378_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
lean_ctor_set(v___x_379_, 2, v___x_377_);
lean_ctor_set(v___x_379_, 3, v___x_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(lean_object* v_as_380_, size_t v_sz_381_, size_t v_i_382_, lean_object* v_b_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_a_397_; uint8_t v___x_401_; 
v___x_401_ = lean_usize_dec_lt(v_i_382_, v_sz_381_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v_b_383_);
return v___x_402_;
}
else
{
lean_object* v_fst_403_; lean_object* v_snd_404_; lean_object* v_a_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_fst_403_ = lean_ctor_get(v_b_383_, 0);
lean_inc(v_fst_403_);
v_snd_404_ = lean_ctor_get(v_b_383_, 1);
lean_inc(v_snd_404_);
lean_dec_ref(v_b_383_);
v_a_405_ = lean_array_uget_borrowed(v_as_380_, v_i_382_);
v___x_406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1));
v___x_407_ = l_Lean_Core_checkSystem(v___x_406_, v___y_393_, v___y_394_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec_ref_known(v___x_407_, 1);
lean_inc(v_a_405_);
v___x_408_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed), 14, 1);
lean_closure_set(v___x_408_, 0, v_a_405_);
v___x_409_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4);
v___x_410_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v___x_408_, v___x_409_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v_fst_412_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v_fst_412_ = lean_ctor_get(v_a_411_, 0);
if (lean_obj_tag(v_fst_412_) == 1)
{
lean_object* v_snd_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_423_; 
lean_inc_ref(v_fst_412_);
v_snd_413_ = lean_ctor_get(v_a_411_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_a_411_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v_a_411_, 0);
lean_dec(v_unused_424_);
v___x_415_ = v_a_411_;
v_isShared_416_ = v_isSharedCheck_423_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_snd_413_);
lean_dec(v_a_411_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_423_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v_val_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v_val_417_ = lean_ctor_get(v_fst_412_, 0);
lean_inc(v_val_417_);
lean_dec_ref_known(v_fst_412_, 1);
v___x_418_ = l_Array_append___redArg(v_fst_403_, v_snd_413_);
lean_dec(v_snd_413_);
v___x_419_ = lean_array_push(v___x_418_, v_val_417_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_snd_404_);
lean_ctor_set(v___x_415_, 0, v___x_419_);
v___x_421_ = v___x_415_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_snd_404_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
v_a_397_ = v___x_421_;
goto v___jp_396_;
}
}
}
else
{
lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_433_; 
v_isSharedCheck_433_ = !lean_is_exclusive(v_a_411_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; lean_object* v_unused_435_; 
v_unused_434_ = lean_ctor_get(v_a_411_, 1);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_a_411_, 0);
lean_dec(v_unused_435_);
v___x_426_ = v_a_411_;
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
else
{
lean_dec(v_a_411_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_428_ = lean_box(0);
lean_inc(v_a_405_);
v___x_429_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_snd_404_, v_a_405_, v___x_428_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_429_);
lean_ctor_set(v___x_426_, 0, v_fst_403_);
v___x_431_ = v___x_426_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_fst_403_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
v_a_397_ = v___x_431_;
goto v___jp_396_;
}
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec(v_snd_404_);
lean_dec(v_fst_403_);
v_a_436_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_410_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_410_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_dec(v_snd_404_);
lean_dec(v_fst_403_);
v_a_444_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_407_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_407_);
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
v___jp_396_:
{
size_t v___x_398_; size_t v___x_399_; 
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_i_382_, v___x_398_);
v_i_382_ = v___x_399_;
v_b_383_ = v_a_397_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___boxed(lean_object* v_as_452_, lean_object* v_sz_453_, lean_object* v_i_454_, lean_object* v_b_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
size_t v_sz_boxed_468_; size_t v_i_boxed_469_; lean_object* v_res_470_; 
v_sz_boxed_468_ = lean_unbox_usize(v_sz_453_);
lean_dec(v_sz_453_);
v_i_boxed_469_ = lean_unbox_usize(v_i_454_);
lean_dec(v_i_454_);
v_res_470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v_as_452_, v_sz_boxed_468_, v_i_boxed_469_, v_b_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec_ref(v_as_452_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(lean_object* v_a_471_, lean_object* v_b_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_array_480_; lean_object* v_start_481_; lean_object* v_stop_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_497_; 
v_array_480_ = lean_ctor_get(v_a_471_, 0);
v_start_481_ = lean_ctor_get(v_a_471_, 1);
v_stop_482_ = lean_ctor_get(v_a_471_, 2);
v_isSharedCheck_497_ = !lean_is_exclusive(v_a_471_);
if (v_isSharedCheck_497_ == 0)
{
v___x_484_ = v_a_471_;
v_isShared_485_ = v_isSharedCheck_497_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_stop_482_);
lean_inc(v_start_481_);
lean_inc(v_array_480_);
lean_dec(v_a_471_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_497_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
uint8_t v___x_486_; 
v___x_486_ = lean_nat_dec_lt(v_start_481_, v_stop_482_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_del_object(v___x_484_);
lean_dec(v_stop_482_);
lean_dec(v_start_481_);
lean_dec_ref(v_array_480_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_b_472_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_add(v_start_481_, v___x_488_);
lean_inc_ref(v_array_480_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v___x_489_);
v___x_491_ = v___x_484_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_array_480_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_stop_482_);
v___x_491_ = v_reuseFailAlloc_496_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_array_fget(v_array_480_, v_start_481_);
lean_dec(v_start_481_);
lean_dec_ref(v_array_480_);
v___x_493_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_b_472_, v___x_492_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v_a_471_ = v___x_491_;
v_b_472_ = v_a_494_;
goto _start;
}
else
{
lean_dec_ref(v___x_491_);
return v___x_493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg___boxed(lean_object* v_a_498_, lean_object* v_b_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_498_, v_b_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_507_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1));
v___x_512_ = l_Lean_MessageData_ofFormat(v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(lean_object* v_sats_513_, lean_object* v_unusedHypotheses_514_, lean_object* v___x_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_hypotheses_528_; lean_object* v___x_529_; size_t v_sz_530_; size_t v___x_531_; lean_object* v___x_532_; 
v_hypotheses_528_ = lean_ctor_get(v___y_516_, 0);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_sats_513_);
lean_ctor_set(v___x_529_, 1, v_unusedHypotheses_514_);
v_sz_530_ = lean_array_size(v_hypotheses_528_);
v___x_531_ = ((size_t)0ULL);
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v_hypotheses_528_, v_sz_530_, v___x_531_, v___x_529_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v_fst_534_; lean_object* v_snd_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_577_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v_fst_534_ = lean_ctor_get(v_a_533_, 0);
v_snd_535_ = lean_ctor_get(v_a_533_, 1);
v_isSharedCheck_577_ = !lean_is_exclusive(v_a_533_);
if (v_isSharedCheck_577_ == 0)
{
v___x_537_ = v_a_533_;
v_isShared_538_ = v_isSharedCheck_577_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_snd_535_);
lean_inc(v_fst_534_);
lean_dec(v_a_533_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_577_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_array_get_size(v_fst_534_);
v___x_540_ = lean_nat_dec_eq(v___x_539_, v___x_515_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_541_ = lean_array_fget(v_fst_534_, v___x_515_);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = l_Array_toSubarray___redArg(v_fst_534_, v___x_542_, v___x_539_);
v___x_544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v___x_543_, v___x_541_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_566_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_566_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_566_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_566_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v_bvExpr_549_; lean_object* v_satAtAtoms_550_; lean_object* v_expr_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_565_; 
v_bvExpr_549_ = lean_ctor_get(v_a_545_, 0);
v_satAtAtoms_550_ = lean_ctor_get(v_a_545_, 1);
v_expr_551_ = lean_ctor_get(v_a_545_, 2);
v_isSharedCheck_565_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_565_ == 0)
{
v___x_553_ = v_a_545_;
v_isShared_554_ = v_isSharedCheck_565_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_expr_551_);
lean_inc(v_satAtAtoms_550_);
lean_inc(v_bvExpr_549_);
lean_dec(v_a_545_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_565_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = l_Lean_ShareCommon_shareCommon___redArg(v_bvExpr_549_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_555_);
v___x_557_ = v___x_553_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_satAtAtoms_550_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_expr_551_);
v___x_557_ = v_reuseFailAlloc_564_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_557_);
v___x_559_ = v___x_537_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_snd_535_);
v___x_559_ = v_reuseFailAlloc_563_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_561_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_559_);
v___x_561_ = v___x_547_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
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
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_del_object(v___x_537_);
lean_dec(v_snd_535_);
v_a_567_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_544_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_544_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_del_object(v___x_537_);
lean_dec(v_snd_535_);
lean_dec(v_fst_534_);
v___x_575_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2);
v___x_576_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v___x_575_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
return v___x_576_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
v_a_578_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_532_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_532_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed(lean_object* v_sats_586_, lean_object* v_unusedHypotheses_587_, lean_object* v___x_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(v_sats_586_, v_unusedHypotheses_587_, v___x_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___x_588_);
return v_res_601_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_box(0);
v___x_603_ = lean_unsigned_to_nat(16u);
v___x_604_ = lean_mk_array(v___x_603_, v___x_602_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v_unusedHypotheses_607_; 
v___x_605_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0);
v___x_606_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_unusedHypotheses_607_, 0, v___x_606_);
lean_ctor_set(v_unusedHypotheses_607_, 1, v___x_605_);
return v_unusedHypotheses_607_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2(void){
_start:
{
lean_object* v___x_608_; lean_object* v_unusedHypotheses_609_; lean_object* v_sats_610_; lean_object* v___f_611_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_609_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1);
v_sats_610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0));
v___f_611_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed), 15, 3);
lean_closure_set(v___f_611_, 0, v_sats_610_);
lean_closure_set(v___f_611_, 1, v_unusedHypotheses_609_);
lean_closure_set(v___f_611_, 2, v___x_608_);
return v___f_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV(lean_object* v_g_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v___f_625_; lean_object* v___x_626_; 
v___f_625_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2);
v___x_626_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_g_612_, v___f_625_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___boxed(lean_object* v_g_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0(lean_object* v_00_u03b2_641_, lean_object* v_m_642_, lean_object* v_a_643_, lean_object* v_b_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_m_642_, v_a_643_, v_b_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(lean_object* v_inst_646_, lean_object* v_R_647_, lean_object* v_a_648_, lean_object* v_b_649_, lean_object* v_c_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_648_, v_b_649_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___boxed(lean_object** _args){
lean_object* v_inst_664_ = _args[0];
lean_object* v_R_665_ = _args[1];
lean_object* v_a_666_ = _args[2];
lean_object* v_b_667_ = _args[3];
lean_object* v_c_668_ = _args[4];
lean_object* v___y_669_ = _args[5];
lean_object* v___y_670_ = _args[6];
lean_object* v___y_671_ = _args[7];
lean_object* v___y_672_ = _args[8];
lean_object* v___y_673_ = _args[9];
lean_object* v___y_674_ = _args[10];
lean_object* v___y_675_ = _args[11];
lean_object* v___y_676_ = _args[12];
lean_object* v___y_677_ = _args[13];
lean_object* v___y_678_ = _args[14];
lean_object* v___y_679_ = _args[15];
lean_object* v___y_680_ = _args[16];
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(v_inst_664_, v_R_665_, v_a_666_, v_b_667_, v_c_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(lean_object* v_00_u03b1_682_, lean_object* v_msg_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_683_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___boxed(lean_object* v_00_u03b1_697_, lean_object* v_msg_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(v_00_u03b1_697_, v_msg_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_711_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(lean_object* v_00_u03b2_712_, lean_object* v_a_713_, lean_object* v_x_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_713_, v_x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___boxed(lean_object* v_00_u03b2_716_, lean_object* v_a_717_, lean_object* v_x_718_){
_start:
{
uint8_t v_res_719_; lean_object* v_r_720_; 
v_res_719_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(v_00_u03b2_716_, v_a_717_, v_x_718_);
lean_dec(v_x_718_);
lean_dec_ref(v_a_717_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1(lean_object* v_00_u03b2_721_, lean_object* v_data_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_data_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_724_, lean_object* v_i_725_, lean_object* v_source_726_, lean_object* v_target_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v_i_725_, v_source_726_, v_target_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_729_, lean_object* v_x_730_, lean_object* v_x_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(v_x_730_, v_x_731_);
return v___x_732_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_unsigned_to_nat(32u);
v___x_734_ = lean_mk_empty_array_with_capacity(v___x_733_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_736_ = ((size_t)5ULL);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_unsigned_to_nat(32u);
v___x_739_ = lean_mk_empty_array_with_capacity(v___x_738_);
v___x_740_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0);
v___x_741_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_739_);
lean_ctor_set(v___x_741_, 2, v___x_737_);
lean_ctor_set(v___x_741_, 3, v___x_737_);
lean_ctor_set_usize(v___x_741_, 4, v___x_736_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; lean_object* v_traceState_745_; lean_object* v_traces_746_; lean_object* v___x_747_; lean_object* v_traceState_748_; lean_object* v_env_749_; lean_object* v_nextMacroScope_750_; lean_object* v_ngen_751_; lean_object* v_auxDeclNGen_752_; lean_object* v_cache_753_; lean_object* v_recordedDeps_754_; lean_object* v_messages_755_; lean_object* v_infoState_756_; lean_object* v_snapshotTasks_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_776_; 
v___x_744_ = lean_st_ref_get(v___y_742_);
v_traceState_745_ = lean_ctor_get(v___x_744_, 4);
lean_inc_ref(v_traceState_745_);
lean_dec(v___x_744_);
v_traces_746_ = lean_ctor_get(v_traceState_745_, 0);
lean_inc_ref(v_traces_746_);
lean_dec_ref(v_traceState_745_);
v___x_747_ = lean_st_ref_take(v___y_742_);
v_traceState_748_ = lean_ctor_get(v___x_747_, 4);
v_env_749_ = lean_ctor_get(v___x_747_, 0);
v_nextMacroScope_750_ = lean_ctor_get(v___x_747_, 1);
v_ngen_751_ = lean_ctor_get(v___x_747_, 2);
v_auxDeclNGen_752_ = lean_ctor_get(v___x_747_, 3);
v_cache_753_ = lean_ctor_get(v___x_747_, 5);
v_recordedDeps_754_ = lean_ctor_get(v___x_747_, 6);
v_messages_755_ = lean_ctor_get(v___x_747_, 7);
v_infoState_756_ = lean_ctor_get(v___x_747_, 8);
v_snapshotTasks_757_ = lean_ctor_get(v___x_747_, 9);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_776_ == 0)
{
v___x_759_ = v___x_747_;
v_isShared_760_ = v_isSharedCheck_776_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_snapshotTasks_757_);
lean_inc(v_infoState_756_);
lean_inc(v_messages_755_);
lean_inc(v_recordedDeps_754_);
lean_inc(v_cache_753_);
lean_inc(v_traceState_748_);
lean_inc(v_auxDeclNGen_752_);
lean_inc(v_ngen_751_);
lean_inc(v_nextMacroScope_750_);
lean_inc(v_env_749_);
lean_dec(v___x_747_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_776_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
uint64_t v_tid_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_774_; 
v_tid_761_ = lean_ctor_get_uint64(v_traceState_748_, sizeof(void*)*1);
v_isSharedCheck_774_ = !lean_is_exclusive(v_traceState_748_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v_traceState_748_, 0);
lean_dec(v_unused_775_);
v___x_763_ = v_traceState_748_;
v_isShared_764_ = v_isSharedCheck_774_;
goto v_resetjp_762_;
}
else
{
lean_dec(v_traceState_748_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_774_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_765_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_765_);
lean_ctor_set_uint64(v_reuseFailAlloc_773_, sizeof(void*)*1, v_tid_761_);
v___x_767_ = v_reuseFailAlloc_773_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 4, v___x_767_);
v___x_769_ = v___x_759_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_env_749_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_nextMacroScope_750_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_ngen_751_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_auxDeclNGen_752_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_772_, 5, v_cache_753_);
lean_ctor_set(v_reuseFailAlloc_772_, 6, v_recordedDeps_754_);
lean_ctor_set(v_reuseFailAlloc_772_, 7, v_messages_755_);
lean_ctor_set(v_reuseFailAlloc_772_, 8, v_infoState_756_);
lean_ctor_set(v_reuseFailAlloc_772_, 9, v_snapshotTasks_757_);
v___x_769_ = v_reuseFailAlloc_772_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_st_ref_put(v___y_742_, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v_traces_746_);
return v___x_771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___boxed(lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v___y_777_);
lean_dec(v___y_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v___y_791_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___boxed(lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
return v_res_807_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(lean_object* v_opts_808_, lean_object* v_opt_809_){
_start:
{
lean_object* v_name_810_; lean_object* v_defValue_811_; lean_object* v_map_812_; lean_object* v___x_813_; 
v_name_810_ = lean_ctor_get(v_opt_809_, 0);
v_defValue_811_ = lean_ctor_get(v_opt_809_, 1);
v_map_812_ = lean_ctor_get(v_opts_808_, 0);
v___x_813_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_812_, v_name_810_);
if (lean_obj_tag(v___x_813_) == 0)
{
uint8_t v___x_814_; 
v___x_814_ = lean_unbox(v_defValue_811_);
return v___x_814_;
}
else
{
lean_object* v_val_815_; 
v_val_815_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_val_815_);
lean_dec_ref_known(v___x_813_, 1);
if (lean_obj_tag(v_val_815_) == 1)
{
uint8_t v_v_816_; 
v_v_816_ = lean_ctor_get_uint8(v_val_815_, 0);
lean_dec_ref_known(v_val_815_, 0);
return v_v_816_;
}
else
{
uint8_t v___x_817_; 
lean_dec(v_val_815_);
v___x_817_ = lean_unbox(v_defValue_811_);
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___boxed(lean_object* v_opts_818_, lean_object* v_opt_819_){
_start:
{
uint8_t v_res_820_; lean_object* v_r_821_; 
v_res_820_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_opts_818_, v_opt_819_);
lean_dec_ref(v_opt_819_);
lean_dec_ref(v_opts_818_);
v_r_821_ = lean_box(v_res_820_);
return v_r_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0(lean_object* v_x_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; 
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
lean_inc(v___y_825_);
lean_inc_ref(v___y_824_);
lean_inc(v___y_823_);
v___x_836_ = lean_apply_13(v_x_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, lean_box(0));
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0___boxed(lean_object* v_x_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0(v_x_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(lean_object* v_mvarId_852_, lean_object* v_x_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___f_867_; lean_object* v___x_868_; 
lean_inc(v___y_861_);
lean_inc_ref(v___y_860_);
lean_inc(v___y_859_);
lean_inc_ref(v___y_858_);
lean_inc(v___y_857_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_854_);
v___f_867_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_867_, 0, v_x_853_);
lean_closure_set(v___f_867_, 1, v___y_854_);
lean_closure_set(v___f_867_, 2, v___y_855_);
lean_closure_set(v___f_867_, 3, v___y_856_);
lean_closure_set(v___f_867_, 4, v___y_857_);
lean_closure_set(v___f_867_, 5, v___y_858_);
lean_closure_set(v___f_867_, 6, v___y_859_);
lean_closure_set(v___f_867_, 7, v___y_860_);
lean_closure_set(v___f_867_, 8, v___y_861_);
v___x_868_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_852_, v___f_867_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_868_) == 0)
{
return v___x_868_;
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___boxed(lean_object* v_mvarId_877_, lean_object* v_x_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(v_mvarId_877_, v_x_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(lean_object* v_00_u03b1_893_, lean_object* v_mvarId_894_, lean_object* v_x_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(v_mvarId_894_, v_x_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___boxed(lean_object* v_00_u03b1_910_, lean_object* v_mvarId_911_, lean_object* v_x_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_00_u03b1_910_, v_mvarId_911_, v_x_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
return v_res_926_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1));
v___x_931_ = l_Lean_MessageData_ofFormat(v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(lean_object* v_x_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed(lean_object* v_x_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(v_x_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v_x_948_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7(lean_object* v_opts_963_, lean_object* v_opt_964_){
_start:
{
lean_object* v_name_965_; lean_object* v_defValue_966_; lean_object* v_map_967_; lean_object* v___x_968_; 
v_name_965_ = lean_ctor_get(v_opt_964_, 0);
v_defValue_966_ = lean_ctor_get(v_opt_964_, 1);
v_map_967_ = lean_ctor_get(v_opts_963_, 0);
v___x_968_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_967_, v_name_965_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_inc(v_defValue_966_);
return v_defValue_966_;
}
else
{
lean_object* v_val_969_; 
v_val_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_val_969_);
lean_dec_ref_known(v___x_968_, 1);
if (lean_obj_tag(v_val_969_) == 3)
{
lean_object* v_v_970_; 
v_v_970_ = lean_ctor_get(v_val_969_, 0);
lean_inc(v_v_970_);
lean_dec_ref_known(v_val_969_, 1);
return v_v_970_;
}
else
{
lean_dec(v_val_969_);
lean_inc(v_defValue_966_);
return v_defValue_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7___boxed(lean_object* v_opts_971_, lean_object* v_opt_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7(v_opts_971_, v_opt_972_);
lean_dec_ref(v_opt_972_);
lean_dec_ref(v_opts_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(lean_object* v_x_974_){
_start:
{
if (lean_obj_tag(v_x_974_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
v_a_976_ = lean_ctor_get(v_x_974_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v_x_974_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v_x_974_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v_x_974_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set_tag(v___x_978_, 1);
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
v_a_984_ = lean_ctor_get(v_x_974_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v_x_974_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v_x_974_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v_x_974_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 0);
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg___boxed(lean_object* v_x_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(v_x_992_);
return v_res_994_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6(lean_object* v_e_995_){
_start:
{
if (lean_obj_tag(v_e_995_) == 0)
{
uint8_t v___x_996_; 
v___x_996_ = 2;
return v___x_996_;
}
else
{
uint8_t v___x_997_; 
v___x_997_ = 0;
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6___boxed(lean_object* v_e_998_){
_start:
{
uint8_t v_res_999_; lean_object* v_r_1000_; 
v_res_999_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6(v_e_998_);
lean_dec_ref(v_e_998_);
v_r_1000_ = lean_box(v_res_999_);
return v_r_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6(size_t v_sz_1001_, size_t v_i_1002_, lean_object* v_bs_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_usize_dec_lt(v_i_1002_, v_sz_1001_);
if (v___x_1004_ == 0)
{
return v_bs_1003_;
}
else
{
lean_object* v_v_1005_; lean_object* v_msg_1006_; lean_object* v___x_1007_; lean_object* v_bs_x27_1008_; size_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1011_; 
v_v_1005_ = lean_array_uget_borrowed(v_bs_1003_, v_i_1002_);
v_msg_1006_ = lean_ctor_get(v_v_1005_, 1);
lean_inc_ref(v_msg_1006_);
v___x_1007_ = lean_unsigned_to_nat(0u);
v_bs_x27_1008_ = lean_array_uset(v_bs_1003_, v_i_1002_, v___x_1007_);
v___x_1009_ = ((size_t)1ULL);
v___x_1010_ = lean_usize_add(v_i_1002_, v___x_1009_);
v___x_1011_ = lean_array_uset(v_bs_x27_1008_, v_i_1002_, v_msg_1006_);
v_i_1002_ = v___x_1010_;
v_bs_1003_ = v___x_1011_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6___boxed(lean_object* v_sz_1013_, lean_object* v_i_1014_, lean_object* v_bs_1015_){
_start:
{
size_t v_sz_boxed_1016_; size_t v_i_boxed_1017_; lean_object* v_res_1018_; 
v_sz_boxed_1016_ = lean_unbox_usize(v_sz_1013_);
lean_dec(v_sz_1013_);
v_i_boxed_1017_ = lean_unbox_usize(v_i_1014_);
lean_dec(v_i_1014_);
v_res_1018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6(v_sz_boxed_1016_, v_i_boxed_1017_, v_bs_1015_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(lean_object* v_oldTraces_1019_, lean_object* v_data_1020_, lean_object* v_ref_1021_, lean_object* v_msg_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_toCold_1028_; lean_object* v_currRecDepth_1029_; lean_object* v_ref_1030_; uint16_t v_optionFlags_1031_; uint8_t v_suppressElabErrors_1032_; uint8_t v_isRecordingDeps_1033_; lean_object* v_ref_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v_traceState_1037_; lean_object* v_traces_1038_; lean_object* v___x_1039_; size_t v_sz_1040_; size_t v___x_1041_; lean_object* v___x_1042_; lean_object* v_msg_1043_; lean_object* v___x_1044_; lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1083_; 
v_toCold_1028_ = lean_ctor_get(v___y_1025_, 0);
v_currRecDepth_1029_ = lean_ctor_get(v___y_1025_, 1);
v_ref_1030_ = lean_ctor_get(v___y_1025_, 2);
v_optionFlags_1031_ = lean_ctor_get_uint16(v___y_1025_, sizeof(void*)*3);
v_suppressElabErrors_1032_ = lean_ctor_get_uint8(v___y_1025_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1033_ = lean_ctor_get_uint8(v___y_1025_, sizeof(void*)*3 + 3);
v_ref_1034_ = l_Lean_replaceRef(v_ref_1021_, v_ref_1030_);
lean_inc(v_currRecDepth_1029_);
lean_inc_ref(v_toCold_1028_);
v___x_1035_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1035_, 0, v_toCold_1028_);
lean_ctor_set(v___x_1035_, 1, v_currRecDepth_1029_);
lean_ctor_set(v___x_1035_, 2, v_ref_1034_);
lean_ctor_set_uint16(v___x_1035_, sizeof(void*)*3, v_optionFlags_1031_);
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*3 + 2, v_suppressElabErrors_1032_);
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*3 + 3, v_isRecordingDeps_1033_);
v___x_1036_ = lean_st_ref_get(v___y_1026_);
v_traceState_1037_ = lean_ctor_get(v___x_1036_, 4);
lean_inc_ref(v_traceState_1037_);
lean_dec(v___x_1036_);
v_traces_1038_ = lean_ctor_get(v_traceState_1037_, 0);
lean_inc_ref(v_traces_1038_);
lean_dec_ref(v_traceState_1037_);
v___x_1039_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1038_);
lean_dec_ref(v_traces_1038_);
v_sz_1040_ = lean_array_size(v___x_1039_);
v___x_1041_ = ((size_t)0ULL);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6(v_sz_1040_, v___x_1041_, v___x_1039_);
v_msg_1043_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1043_, 0, v_data_1020_);
lean_ctor_set(v_msg_1043_, 1, v_msg_1022_);
lean_ctor_set(v_msg_1043_, 2, v___x_1042_);
v___x_1044_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_1043_, v___y_1023_, v___y_1024_, v___x_1035_, v___y_1026_);
lean_dec_ref_known(v___x_1035_, 3);
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1083_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1083_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v_traceState_1050_; lean_object* v_env_1051_; lean_object* v_nextMacroScope_1052_; lean_object* v_ngen_1053_; lean_object* v_auxDeclNGen_1054_; lean_object* v_cache_1055_; lean_object* v_recordedDeps_1056_; lean_object* v_messages_1057_; lean_object* v_infoState_1058_; lean_object* v_snapshotTasks_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1082_; 
v___x_1049_ = lean_st_ref_take(v___y_1026_);
v_traceState_1050_ = lean_ctor_get(v___x_1049_, 4);
v_env_1051_ = lean_ctor_get(v___x_1049_, 0);
v_nextMacroScope_1052_ = lean_ctor_get(v___x_1049_, 1);
v_ngen_1053_ = lean_ctor_get(v___x_1049_, 2);
v_auxDeclNGen_1054_ = lean_ctor_get(v___x_1049_, 3);
v_cache_1055_ = lean_ctor_get(v___x_1049_, 5);
v_recordedDeps_1056_ = lean_ctor_get(v___x_1049_, 6);
v_messages_1057_ = lean_ctor_get(v___x_1049_, 7);
v_infoState_1058_ = lean_ctor_get(v___x_1049_, 8);
v_snapshotTasks_1059_ = lean_ctor_get(v___x_1049_, 9);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1061_ = v___x_1049_;
v_isShared_1062_ = v_isSharedCheck_1082_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_snapshotTasks_1059_);
lean_inc(v_infoState_1058_);
lean_inc(v_messages_1057_);
lean_inc(v_recordedDeps_1056_);
lean_inc(v_cache_1055_);
lean_inc(v_traceState_1050_);
lean_inc(v_auxDeclNGen_1054_);
lean_inc(v_ngen_1053_);
lean_inc(v_nextMacroScope_1052_);
lean_inc(v_env_1051_);
lean_dec(v___x_1049_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1082_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
uint64_t v_tid_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1080_; 
v_tid_1063_ = lean_ctor_get_uint64(v_traceState_1050_, sizeof(void*)*1);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_traceState_1050_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v_traceState_1050_, 0);
lean_dec(v_unused_1081_);
v___x_1065_ = v_traceState_1050_;
v_isShared_1066_ = v_isSharedCheck_1080_;
goto v_resetjp_1064_;
}
else
{
lean_dec(v_traceState_1050_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1080_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_ref_1021_);
lean_ctor_set(v___x_1068_, 1, v_a_1045_);
v___x_1069_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1019_, v___x_1068_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1069_);
v___x_1071_ = v___x_1065_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1069_);
lean_ctor_set_uint64(v_reuseFailAlloc_1079_, sizeof(void*)*1, v_tid_1063_);
v___x_1071_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1073_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 4, v___x_1071_);
v___x_1073_ = v___x_1061_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_env_1051_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_nextMacroScope_1052_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_ngen_1053_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v_auxDeclNGen_1054_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1078_, 5, v_cache_1055_);
lean_ctor_set(v_reuseFailAlloc_1078_, 6, v_recordedDeps_1056_);
lean_ctor_set(v_reuseFailAlloc_1078_, 7, v_messages_1057_);
lean_ctor_set(v_reuseFailAlloc_1078_, 8, v_infoState_1058_);
lean_ctor_set(v_reuseFailAlloc_1078_, 9, v_snapshotTasks_1059_);
v___x_1073_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_st_ref_put(v___y_1026_, v___x_1073_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1067_);
v___x_1076_ = v___x_1047_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1067_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg___boxed(lean_object* v_oldTraces_1084_, lean_object* v_data_1085_, lean_object* v_ref_1086_, lean_object* v_msg_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(v_oldTraces_1084_, v_data_1085_, v_ref_1086_, v_msg_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1093_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1094_; double v___x_1095_; 
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = lean_float_of_nat(v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__1));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1099_; double v___x_1100_; 
v___x_1099_ = lean_unsigned_to_nat(1000u);
v___x_1100_ = lean_float_of_nat(v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(lean_object* v_cls_1101_, uint8_t v_collapsed_1102_, lean_object* v_tag_1103_, lean_object* v_opts_1104_, uint8_t v_clsEnabled_1105_, lean_object* v_oldTraces_1106_, lean_object* v_msg_1107_, lean_object* v_resStartStop_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_fst_1122_; lean_object* v_snd_1123_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v_data_1127_; lean_object* v_fst_1138_; lean_object* v_snd_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; lean_object* v___y_1143_; lean_object* v_a_1144_; uint8_t v___y_1159_; double v___y_1191_; 
v_fst_1122_ = lean_ctor_get(v_resStartStop_1108_, 0);
lean_inc(v_fst_1122_);
v_snd_1123_ = lean_ctor_get(v_resStartStop_1108_, 1);
lean_inc(v_snd_1123_);
lean_dec_ref(v_resStartStop_1108_);
v_fst_1138_ = lean_ctor_get(v_snd_1123_, 0);
lean_inc(v_fst_1138_);
v_snd_1139_ = lean_ctor_get(v_snd_1123_, 1);
lean_inc(v_snd_1139_);
lean_dec(v_snd_1123_);
v___x_1140_ = l_Lean_trace_profiler;
v___x_1141_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_opts_1104_, v___x_1140_);
if (v___x_1141_ == 0)
{
v___y_1159_ = v___x_1141_;
goto v___jp_1158_;
}
else
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1197_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_opts_1104_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; double v___x_1200_; double v___x_1201_; double v___x_1202_; 
v___x_1198_ = l_Lean_trace_profiler_threshold;
v___x_1199_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7(v_opts_1104_, v___x_1198_);
v___x_1200_ = lean_float_of_nat(v___x_1199_);
v___x_1201_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3);
v___x_1202_ = lean_float_div(v___x_1200_, v___x_1201_);
v___y_1191_ = v___x_1202_;
goto v___jp_1190_;
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; double v___x_1205_; 
v___x_1203_ = l_Lean_trace_profiler_threshold;
v___x_1204_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7(v_opts_1104_, v___x_1203_);
v___x_1205_ = lean_float_of_nat(v___x_1204_);
v___y_1191_ = v___x_1205_;
goto v___jp_1190_;
}
}
v___jp_1124_:
{
lean_object* v___x_1128_; 
lean_inc(v___y_1126_);
v___x_1128_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(v_oldTraces_1106_, v_data_1127_, v___y_1126_, v___y_1125_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v___x_1129_; 
lean_dec_ref_known(v___x_1128_, 1);
v___x_1129_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(v_fst_1122_);
return v___x_1129_;
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v_fst_1122_);
v_a_1130_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1128_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1128_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
v___jp_1142_:
{
uint8_t v_result_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; double v___x_1148_; lean_object* v_data_1149_; 
v_result_1145_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6(v_fst_1122_);
v___x_1146_ = lean_box(v_result_1145_);
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
v___x_1148_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0);
lean_inc_ref(v_tag_1103_);
lean_inc_ref(v___x_1147_);
lean_inc(v_cls_1101_);
v_data_1149_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1149_, 0, v_cls_1101_);
lean_ctor_set(v_data_1149_, 1, v___x_1147_);
lean_ctor_set(v_data_1149_, 2, v_tag_1103_);
lean_ctor_set_float(v_data_1149_, sizeof(void*)*3, v___x_1148_);
lean_ctor_set_float(v_data_1149_, sizeof(void*)*3 + 8, v___x_1148_);
lean_ctor_set_uint8(v_data_1149_, sizeof(void*)*3 + 16, v_collapsed_1102_);
if (v___x_1141_ == 0)
{
lean_dec_ref_known(v___x_1147_, 1);
lean_dec(v_snd_1139_);
lean_dec(v_fst_1138_);
lean_dec_ref(v_tag_1103_);
lean_dec(v_cls_1101_);
v___y_1125_ = v_a_1144_;
v___y_1126_ = v___y_1143_;
v_data_1127_ = v_data_1149_;
goto v___jp_1124_;
}
else
{
lean_object* v_data_1150_; double v___x_1151_; double v___x_1152_; 
lean_dec_ref_known(v_data_1149_, 3);
v_data_1150_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1150_, 0, v_cls_1101_);
lean_ctor_set(v_data_1150_, 1, v___x_1147_);
lean_ctor_set(v_data_1150_, 2, v_tag_1103_);
v___x_1151_ = lean_unbox_float(v_fst_1138_);
lean_dec(v_fst_1138_);
lean_ctor_set_float(v_data_1150_, sizeof(void*)*3, v___x_1151_);
v___x_1152_ = lean_unbox_float(v_snd_1139_);
lean_dec(v_snd_1139_);
lean_ctor_set_float(v_data_1150_, sizeof(void*)*3 + 8, v___x_1152_);
lean_ctor_set_uint8(v_data_1150_, sizeof(void*)*3 + 16, v_collapsed_1102_);
v___y_1125_ = v_a_1144_;
v___y_1126_ = v___y_1143_;
v_data_1127_ = v_data_1150_;
goto v___jp_1124_;
}
}
v___jp_1153_:
{
lean_object* v_ref_1154_; lean_object* v___x_1155_; 
v_ref_1154_ = lean_ctor_get(v___y_1119_, 2);
lean_inc(v___y_1120_);
lean_inc_ref(v___y_1119_);
lean_inc(v___y_1118_);
lean_inc_ref(v___y_1117_);
lean_inc(v___y_1116_);
lean_inc_ref(v___y_1115_);
lean_inc(v___y_1114_);
lean_inc_ref(v___y_1113_);
lean_inc(v___y_1112_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1110_);
lean_inc(v___y_1109_);
lean_inc(v_fst_1122_);
v___x_1155_ = lean_apply_14(v_msg_1107_, v_fst_1122_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, lean_box(0));
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___y_1143_ = v_ref_1154_;
v_a_1144_ = v_a_1156_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1157_; 
lean_dec_ref_known(v___x_1155_, 1);
v___x_1157_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2);
v___y_1143_ = v_ref_1154_;
v_a_1144_ = v___x_1157_;
goto v___jp_1142_;
}
}
v___jp_1158_:
{
if (v_clsEnabled_1105_ == 0)
{
if (v___y_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v_traceState_1161_; lean_object* v_env_1162_; lean_object* v_nextMacroScope_1163_; lean_object* v_ngen_1164_; lean_object* v_auxDeclNGen_1165_; lean_object* v_cache_1166_; lean_object* v_recordedDeps_1167_; lean_object* v_messages_1168_; lean_object* v_infoState_1169_; lean_object* v_snapshotTasks_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1189_; 
lean_dec(v_snd_1139_);
lean_dec(v_fst_1138_);
lean_dec_ref(v_msg_1107_);
lean_dec_ref(v_tag_1103_);
lean_dec(v_cls_1101_);
v___x_1160_ = lean_st_ref_take(v___y_1120_);
v_traceState_1161_ = lean_ctor_get(v___x_1160_, 4);
v_env_1162_ = lean_ctor_get(v___x_1160_, 0);
v_nextMacroScope_1163_ = lean_ctor_get(v___x_1160_, 1);
v_ngen_1164_ = lean_ctor_get(v___x_1160_, 2);
v_auxDeclNGen_1165_ = lean_ctor_get(v___x_1160_, 3);
v_cache_1166_ = lean_ctor_get(v___x_1160_, 5);
v_recordedDeps_1167_ = lean_ctor_get(v___x_1160_, 6);
v_messages_1168_ = lean_ctor_get(v___x_1160_, 7);
v_infoState_1169_ = lean_ctor_get(v___x_1160_, 8);
v_snapshotTasks_1170_ = lean_ctor_get(v___x_1160_, 9);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1172_ = v___x_1160_;
v_isShared_1173_ = v_isSharedCheck_1189_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_snapshotTasks_1170_);
lean_inc(v_infoState_1169_);
lean_inc(v_messages_1168_);
lean_inc(v_recordedDeps_1167_);
lean_inc(v_cache_1166_);
lean_inc(v_traceState_1161_);
lean_inc(v_auxDeclNGen_1165_);
lean_inc(v_ngen_1164_);
lean_inc(v_nextMacroScope_1163_);
lean_inc(v_env_1162_);
lean_dec(v___x_1160_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1189_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
uint64_t v_tid_1174_; lean_object* v_traces_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1188_; 
v_tid_1174_ = lean_ctor_get_uint64(v_traceState_1161_, sizeof(void*)*1);
v_traces_1175_ = lean_ctor_get(v_traceState_1161_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_traceState_1161_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1177_ = v_traceState_1161_;
v_isShared_1178_ = v_isSharedCheck_1188_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_traces_1175_);
lean_dec(v_traceState_1161_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1188_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1106_, v_traces_1175_);
lean_dec_ref(v_traces_1175_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1179_);
lean_ctor_set_uint64(v_reuseFailAlloc_1187_, sizeof(void*)*1, v_tid_1174_);
v___x_1181_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1183_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 4, v___x_1181_);
v___x_1183_ = v___x_1172_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_env_1162_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_nextMacroScope_1163_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_ngen_1164_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v_auxDeclNGen_1165_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1186_, 5, v_cache_1166_);
lean_ctor_set(v_reuseFailAlloc_1186_, 6, v_recordedDeps_1167_);
lean_ctor_set(v_reuseFailAlloc_1186_, 7, v_messages_1168_);
lean_ctor_set(v_reuseFailAlloc_1186_, 8, v_infoState_1169_);
lean_ctor_set(v_reuseFailAlloc_1186_, 9, v_snapshotTasks_1170_);
v___x_1183_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_st_ref_put(v___y_1120_, v___x_1183_);
v___x_1185_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(v_fst_1122_);
return v___x_1185_;
}
}
}
}
}
else
{
goto v___jp_1153_;
}
}
else
{
goto v___jp_1153_;
}
}
v___jp_1190_:
{
double v___x_1192_; double v___x_1193_; double v___x_1194_; uint8_t v___x_1195_; 
v___x_1192_ = lean_unbox_float(v_snd_1139_);
v___x_1193_ = lean_unbox_float(v_fst_1138_);
v___x_1194_ = lean_float_sub(v___x_1192_, v___x_1193_);
v___x_1195_ = lean_float_decLt(v___y_1191_, v___x_1194_);
v___y_1159_ = v___x_1195_;
goto v___jp_1158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___boxed(lean_object** _args){
lean_object* v_cls_1206_ = _args[0];
lean_object* v_collapsed_1207_ = _args[1];
lean_object* v_tag_1208_ = _args[2];
lean_object* v_opts_1209_ = _args[3];
lean_object* v_clsEnabled_1210_ = _args[4];
lean_object* v_oldTraces_1211_ = _args[5];
lean_object* v_msg_1212_ = _args[6];
lean_object* v_resStartStop_1213_ = _args[7];
lean_object* v___y_1214_ = _args[8];
lean_object* v___y_1215_ = _args[9];
lean_object* v___y_1216_ = _args[10];
lean_object* v___y_1217_ = _args[11];
lean_object* v___y_1218_ = _args[12];
lean_object* v___y_1219_ = _args[13];
lean_object* v___y_1220_ = _args[14];
lean_object* v___y_1221_ = _args[15];
lean_object* v___y_1222_ = _args[16];
lean_object* v___y_1223_ = _args[17];
lean_object* v___y_1224_ = _args[18];
lean_object* v___y_1225_ = _args[19];
lean_object* v___y_1226_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_1227_; uint8_t v_clsEnabled_boxed_1228_; lean_object* v_res_1229_; 
v_collapsed_boxed_1227_ = lean_unbox(v_collapsed_1207_);
v_clsEnabled_boxed_1228_ = lean_unbox(v_clsEnabled_1210_);
v_res_1229_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_cls_1206_, v_collapsed_boxed_1227_, v_tag_1208_, v_opts_1209_, v_clsEnabled_boxed_1228_, v_oldTraces_1211_, v_msg_1212_, v_resStartStop_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v_opts_1209_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(lean_object* v_cls_1233_, lean_object* v_msg_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_ref_1240_; lean_object* v___x_1241_; lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1287_; 
v_ref_1240_ = lean_ctor_get(v___y_1237_, 2);
v___x_1241_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1287_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1287_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v_traceState_1247_; lean_object* v_env_1248_; lean_object* v_nextMacroScope_1249_; lean_object* v_ngen_1250_; lean_object* v_auxDeclNGen_1251_; lean_object* v_cache_1252_; lean_object* v_recordedDeps_1253_; lean_object* v_messages_1254_; lean_object* v_infoState_1255_; lean_object* v_snapshotTasks_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1286_; 
v___x_1246_ = lean_st_ref_take(v___y_1238_);
v_traceState_1247_ = lean_ctor_get(v___x_1246_, 4);
v_env_1248_ = lean_ctor_get(v___x_1246_, 0);
v_nextMacroScope_1249_ = lean_ctor_get(v___x_1246_, 1);
v_ngen_1250_ = lean_ctor_get(v___x_1246_, 2);
v_auxDeclNGen_1251_ = lean_ctor_get(v___x_1246_, 3);
v_cache_1252_ = lean_ctor_get(v___x_1246_, 5);
v_recordedDeps_1253_ = lean_ctor_get(v___x_1246_, 6);
v_messages_1254_ = lean_ctor_get(v___x_1246_, 7);
v_infoState_1255_ = lean_ctor_get(v___x_1246_, 8);
v_snapshotTasks_1256_ = lean_ctor_get(v___x_1246_, 9);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1258_ = v___x_1246_;
v_isShared_1259_ = v_isSharedCheck_1286_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_snapshotTasks_1256_);
lean_inc(v_infoState_1255_);
lean_inc(v_messages_1254_);
lean_inc(v_recordedDeps_1253_);
lean_inc(v_cache_1252_);
lean_inc(v_traceState_1247_);
lean_inc(v_auxDeclNGen_1251_);
lean_inc(v_ngen_1250_);
lean_inc(v_nextMacroScope_1249_);
lean_inc(v_env_1248_);
lean_dec(v___x_1246_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1286_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
uint64_t v_tid_1260_; lean_object* v_traces_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1285_; 
v_tid_1260_ = lean_ctor_get_uint64(v_traceState_1247_, sizeof(void*)*1);
v_traces_1261_ = lean_ctor_get(v_traceState_1247_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_traceState_1247_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1263_ = v_traceState_1247_;
v_isShared_1264_ = v_isSharedCheck_1285_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_traces_1261_);
lean_dec(v_traceState_1247_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1285_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; double v___x_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_box(0);
v___x_1267_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0);
v___x_1268_ = 0;
v___x_1269_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__0));
v___x_1270_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1270_, 0, v_cls_1233_);
lean_ctor_set(v___x_1270_, 1, v___x_1266_);
lean_ctor_set(v___x_1270_, 2, v___x_1269_);
lean_ctor_set_float(v___x_1270_, sizeof(void*)*3, v___x_1267_);
lean_ctor_set_float(v___x_1270_, sizeof(void*)*3 + 8, v___x_1267_);
lean_ctor_set_uint8(v___x_1270_, sizeof(void*)*3 + 16, v___x_1268_);
v___x_1271_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__1));
v___x_1272_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1270_);
lean_ctor_set(v___x_1272_, 1, v_a_1242_);
lean_ctor_set(v___x_1272_, 2, v___x_1271_);
lean_inc(v_ref_1240_);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v_ref_1240_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = l_Lean_PersistentArray_push___redArg(v_traces_1261_, v___x_1273_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1274_);
v___x_1276_ = v___x_1263_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1274_);
lean_ctor_set_uint64(v_reuseFailAlloc_1284_, sizeof(void*)*1, v_tid_1260_);
v___x_1276_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 4, v___x_1276_);
v___x_1278_ = v___x_1258_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_env_1248_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_nextMacroScope_1249_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_ngen_1250_);
lean_ctor_set(v_reuseFailAlloc_1283_, 3, v_auxDeclNGen_1251_);
lean_ctor_set(v_reuseFailAlloc_1283_, 4, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1283_, 5, v_cache_1252_);
lean_ctor_set(v_reuseFailAlloc_1283_, 6, v_recordedDeps_1253_);
lean_ctor_set(v_reuseFailAlloc_1283_, 7, v_messages_1254_);
lean_ctor_set(v_reuseFailAlloc_1283_, 8, v_infoState_1255_);
lean_ctor_set(v_reuseFailAlloc_1283_, 9, v_snapshotTasks_1256_);
v___x_1278_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1279_ = lean_st_ref_put(v___y_1238_, v___x_1278_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1265_);
v___x_1281_ = v___x_1244_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1265_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___boxed(lean_object* v_cls_1288_, lean_object* v_msg_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(v_cls_1288_, v_msg_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(lean_object* v_x_1303_){
_start:
{
switch(lean_obj_tag(v_x_1303_))
{
case 0:
{
lean_object* v_a_1304_; lean_object* v___x_1305_; 
v_a_1304_ = lean_ctor_get(v_x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v_x_1303_, 1);
v___x_1305_ = l_Std_Tactic_BVDecide_BVPred_toString(v_a_1304_);
return v___x_1305_;
}
case 1:
{
uint8_t v_a_1306_; 
v_a_1306_ = lean_ctor_get_uint8(v_x_1303_, 0);
lean_dec_ref_known(v_x_1303_, 0);
if (v_a_1306_ == 0)
{
lean_object* v___x_1307_; 
v___x_1307_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__0));
return v___x_1307_;
}
else
{
lean_object* v___x_1308_; 
v___x_1308_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__1));
return v___x_1308_;
}
}
case 2:
{
lean_object* v_a_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_a_1309_ = lean_ctor_get(v_x_1303_, 0);
lean_inc_ref(v_a_1309_);
lean_dec_ref_known(v_x_1303_, 1);
v___x_1310_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__2));
v___x_1311_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1309_);
v___x_1312_ = lean_string_append(v___x_1310_, v___x_1311_);
lean_dec_ref(v___x_1311_);
return v___x_1312_;
}
case 3:
{
uint8_t v_a_1313_; lean_object* v_a_1314_; lean_object* v_a_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_a_1313_ = lean_ctor_get_uint8(v_x_1303_, sizeof(void*)*2);
v_a_1314_ = lean_ctor_get(v_x_1303_, 0);
lean_inc_ref(v_a_1314_);
v_a_1315_ = lean_ctor_get(v_x_1303_, 1);
lean_inc_ref(v_a_1315_);
lean_dec_ref_known(v_x_1303_, 2);
v___x_1316_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__3));
v___x_1317_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1314_);
v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
lean_dec_ref(v___x_1317_);
v___x_1319_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__4));
v___x_1320_ = lean_string_append(v___x_1318_, v___x_1319_);
v___x_1321_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_1313_);
v___x_1322_ = lean_string_append(v___x_1320_, v___x_1321_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = lean_string_append(v___x_1322_, v___x_1319_);
v___x_1324_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1315_);
v___x_1325_ = lean_string_append(v___x_1323_, v___x_1324_);
lean_dec_ref(v___x_1324_);
v___x_1326_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__5));
v___x_1327_ = lean_string_append(v___x_1325_, v___x_1326_);
return v___x_1327_;
}
default: 
{
lean_object* v_a_1328_; lean_object* v_a_1329_; lean_object* v_a_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_a_1328_ = lean_ctor_get(v_x_1303_, 0);
lean_inc_ref(v_a_1328_);
v_a_1329_ = lean_ctor_get(v_x_1303_, 1);
lean_inc_ref(v_a_1329_);
v_a_1330_ = lean_ctor_get(v_x_1303_, 2);
lean_inc_ref(v_a_1330_);
lean_dec_ref_known(v_x_1303_, 3);
v___x_1331_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__6));
v___x_1332_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1328_);
v___x_1333_ = lean_string_append(v___x_1331_, v___x_1332_);
lean_dec_ref(v___x_1332_);
v___x_1334_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__4));
v___x_1335_ = lean_string_append(v___x_1333_, v___x_1334_);
v___x_1336_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1329_);
v___x_1337_ = lean_string_append(v___x_1335_, v___x_1336_);
lean_dec_ref(v___x_1336_);
v___x_1338_ = lean_string_append(v___x_1337_, v___x_1334_);
v___x_1339_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1330_);
v___x_1340_ = lean_string_append(v___x_1338_, v___x_1339_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__5));
v___x_1342_ = lean_string_append(v___x_1340_, v___x_1341_);
return v___x_1342_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2));
v___x_1348_ = l_Lean_stringToMessageData(v___x_1347_);
return v___x_1348_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1349_; double v___x_1350_; 
v___x_1349_ = lean_unsigned_to_nat(1000000000u);
v___x_1350_ = lean_float_of_nat(v___x_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(lean_object* v_unsatProver_1351_, lean_object* v_g_1352_, lean_object* v_cls_1353_, uint8_t v___x_1354_, lean_object* v___x_1355_, lean_object* v___f_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_toCold_1370_; lean_object* v_options_1371_; lean_object* v_inheritedTraceOptions_1372_; uint8_t v_hasTrace_1373_; lean_object* v___y_1375_; 
v_toCold_1370_ = lean_ctor_get(v___y_1367_, 0);
v_options_1371_ = lean_ctor_get(v_toCold_1370_, 2);
v_inheritedTraceOptions_1372_ = lean_ctor_get(v_toCold_1370_, 11);
v_hasTrace_1373_ = lean_ctor_get_uint8(v_options_1371_, sizeof(void*)*1);
if (v_hasTrace_1373_ == 0)
{
lean_object* v___x_1408_; 
lean_dec_ref(v___f_1356_);
lean_dec_ref(v___x_1355_);
lean_inc(v_g_1352_);
v___x_1408_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1352_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
v___y_1375_ = v___x_1408_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v_a_1415_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v_a_1430_; 
v___x_1409_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1));
lean_inc(v_cls_1353_);
v___x_1410_ = l_Lean_Name_append(v___x_1409_, v_cls_1353_);
v___x_1411_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1372_, v_options_1371_, v___x_1410_);
lean_dec(v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = l_Lean_trace_profiler;
v___x_1481_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_options_1371_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
lean_dec_ref(v___f_1356_);
lean_dec_ref(v___x_1355_);
lean_inc(v_g_1352_);
v___x_1482_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1352_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
v___y_1375_ = v___x_1482_;
goto v___jp_1374_;
}
else
{
goto v___jp_1439_;
}
}
else
{
goto v___jp_1439_;
}
v___jp_1412_:
{
lean_object* v___x_1416_; double v___x_1417_; double v___x_1418_; double v___x_1419_; double v___x_1420_; double v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1416_ = lean_io_mono_nanos_now();
v___x_1417_ = lean_float_of_nat(v___y_1414_);
v___x_1418_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4);
v___x_1419_ = lean_float_div(v___x_1417_, v___x_1418_);
v___x_1420_ = lean_float_of_nat(v___x_1416_);
v___x_1421_ = lean_float_div(v___x_1420_, v___x_1418_);
v___x_1422_ = lean_box_float(v___x_1419_);
v___x_1423_ = lean_box_float(v___x_1421_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_a_1415_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
lean_inc(v_cls_1353_);
v___x_1426_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_cls_1353_, v___x_1354_, v___x_1355_, v_options_1371_, v___x_1411_, v___y_1413_, v___f_1356_, v___x_1425_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
v___y_1375_ = v___x_1426_;
goto v___jp_1374_;
}
v___jp_1427_:
{
lean_object* v___x_1431_; double v___x_1432_; double v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1431_ = lean_io_get_num_heartbeats();
v___x_1432_ = lean_float_of_nat(v___y_1429_);
v___x_1433_ = lean_float_of_nat(v___x_1431_);
v___x_1434_ = lean_box_float(v___x_1432_);
v___x_1435_ = lean_box_float(v___x_1433_);
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1434_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_a_1430_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
lean_inc(v_cls_1353_);
v___x_1438_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_cls_1353_, v___x_1354_, v___x_1355_, v_options_1371_, v___x_1411_, v___y_1428_, v___f_1356_, v___x_1437_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
v___y_1375_ = v___x_1438_;
goto v___jp_1374_;
}
v___jp_1439_:
{
lean_object* v___x_1440_; lean_object* v_a_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1440_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v___y_1368_);
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref(v___x_1440_);
v___x_1442_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1443_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_options_1371_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_io_mono_nanos_now();
lean_inc(v_g_1352_);
v___x_1445_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1352_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1445_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1445_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set_tag(v___x_1448_, 1);
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
v___y_1413_ = v_a_1441_;
v___y_1414_ = v___x_1444_;
v_a_1415_ = v___x_1451_;
goto v___jp_1412_;
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
v_a_1454_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1445_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1445_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set_tag(v___x_1456_, 0);
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
v___y_1413_ = v_a_1441_;
v___y_1414_ = v___x_1444_;
v_a_1415_ = v___x_1459_;
goto v___jp_1412_;
}
}
}
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_io_get_num_heartbeats();
lean_inc(v_g_1352_);
v___x_1463_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1352_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set_tag(v___x_1466_, 1);
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
v___y_1428_ = v_a_1441_;
v___y_1429_ = v___x_1462_;
v_a_1430_ = v___x_1469_;
goto v___jp_1427_;
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
v_a_1472_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1463_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1463_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set_tag(v___x_1474_, 0);
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
v___y_1428_ = v_a_1441_;
v___y_1429_ = v___x_1462_;
v_a_1430_ = v___x_1477_;
goto v___jp_1427_;
}
}
}
}
}
}
v___jp_1374_:
{
if (lean_obj_tag(v___y_1375_) == 0)
{
if (v_hasTrace_1373_ == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; 
lean_dec(v_cls_1353_);
v_a_1376_ = lean_ctor_get(v___y_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___y_1375_, 1);
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
lean_inc(v___y_1362_);
lean_inc_ref(v___y_1361_);
lean_inc(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc(v___y_1357_);
v___x_1377_ = lean_apply_15(v_unsatProver_1351_, v_g_1352_, v_a_1376_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, lean_box(0));
return v___x_1377_;
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v_a_1378_ = lean_ctor_get(v___y_1375_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___y_1375_, 1);
v___x_1379_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1));
lean_inc(v_cls_1353_);
v___x_1380_ = l_Lean_Name_append(v___x_1379_, v_cls_1353_);
v___x_1381_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1372_, v_options_1371_, v___x_1380_);
lean_dec(v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec(v_cls_1353_);
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
lean_inc(v___y_1362_);
lean_inc_ref(v___y_1361_);
lean_inc(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc(v___y_1357_);
v___x_1382_ = lean_apply_15(v_unsatProver_1351_, v_g_1352_, v_a_1378_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, lean_box(0));
return v___x_1382_;
}
else
{
lean_object* v_satExpr_1383_; lean_object* v_bvExpr_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_satExpr_1383_ = lean_ctor_get(v_a_1378_, 0);
v_bvExpr_1384_ = lean_ctor_get(v_satExpr_1383_, 0);
v___x_1385_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3);
lean_inc_ref(v_bvExpr_1384_);
v___x_1386_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_bvExpr_1384_);
v___x_1387_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
v___x_1388_ = l_Lean_MessageData_ofFormat(v___x_1387_);
v___x_1389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1385_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(v_cls_1353_, v___x_1389_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v___x_1391_; 
lean_dec_ref_known(v___x_1390_, 1);
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
lean_inc(v___y_1362_);
lean_inc_ref(v___y_1361_);
lean_inc(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc(v___y_1357_);
v___x_1391_ = lean_apply_15(v_unsatProver_1351_, v_g_1352_, v_a_1378_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, lean_box(0));
return v___x_1391_;
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec(v_a_1378_);
lean_dec(v_g_1352_);
lean_dec_ref(v_unsatProver_1351_);
v_a_1392_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1390_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1390_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_cls_1353_);
lean_dec(v_g_1352_);
lean_dec_ref(v_unsatProver_1351_);
v_a_1400_ = lean_ctor_get(v___y_1375_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___y_1375_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___y_1375_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___y_1375_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_unsatProver_1483_ = _args[0];
lean_object* v_g_1484_ = _args[1];
lean_object* v_cls_1485_ = _args[2];
lean_object* v___x_1486_ = _args[3];
lean_object* v___x_1487_ = _args[4];
lean_object* v___f_1488_ = _args[5];
lean_object* v___y_1489_ = _args[6];
lean_object* v___y_1490_ = _args[7];
lean_object* v___y_1491_ = _args[8];
lean_object* v___y_1492_ = _args[9];
lean_object* v___y_1493_ = _args[10];
lean_object* v___y_1494_ = _args[11];
lean_object* v___y_1495_ = _args[12];
lean_object* v___y_1496_ = _args[13];
lean_object* v___y_1497_ = _args[14];
lean_object* v___y_1498_ = _args[15];
lean_object* v___y_1499_ = _args[16];
lean_object* v___y_1500_ = _args[17];
lean_object* v___y_1501_ = _args[18];
_start:
{
uint8_t v___x_64518__boxed_1502_; lean_object* v_res_1503_; 
v___x_64518__boxed_1502_ = lean_unbox(v___x_1486_);
v_res_1503_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(v_unsatProver_1483_, v_g_1484_, v_cls_1485_, v___x_64518__boxed_1502_, v___x_1487_, v___f_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(lean_object* v_g_1512_, lean_object* v_unsatProver_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v___f_1526_; lean_object* v_cls_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___f_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___f_1526_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0));
v_cls_1527_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4));
v___x_1528_ = 1;
v___x_1529_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__0));
v___x_1530_ = lean_box(v___x_1528_);
lean_inc(v_g_1512_);
v___f_1531_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed), 19, 6);
lean_closure_set(v___f_1531_, 0, v_unsatProver_1513_);
lean_closure_set(v___f_1531_, 1, v_g_1512_);
lean_closure_set(v___f_1531_, 2, v_cls_1527_);
lean_closure_set(v___f_1531_, 3, v___x_1530_);
lean_closure_set(v___f_1531_, 4, v___x_1529_);
lean_closure_set(v___f_1531_, 5, v___f_1526_);
v___x_1532_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___boxed), 16, 3);
lean_closure_set(v___x_1532_, 0, lean_box(0));
lean_closure_set(v___x_1532_, 1, v_g_1512_);
lean_closure_set(v___x_1532_, 2, v___f_1531_);
v___x_1533_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4);
v___x_1534_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v___x_1532_, v___x_1533_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1543_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1543_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1543_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v_fst_1539_; lean_object* v___x_1541_; 
v_fst_1539_ = lean_ctor_get(v_a_1535_, 0);
lean_inc(v_fst_1539_);
lean_dec(v_a_1535_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v_fst_1539_);
v___x_1541_ = v___x_1537_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_fst_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
v_a_1544_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1534_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1534_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___boxed(lean_object* v_g_1552_, lean_object* v_unsatProver_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1552_, v_unsatProver_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
lean_dec(v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(lean_object* v_00_u03b1_1567_, lean_object* v_g_1568_, lean_object* v_unsatProver_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1568_, v_unsatProver_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed(lean_object* v_00_u03b1_1583_, lean_object* v_g_1584_, lean_object* v_unsatProver_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(v_00_u03b1_1583_, v_g_1584_, v_unsatProver_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(lean_object* v_cls_1599_, lean_object* v_msg_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(v_cls_1599_, v_msg_1600_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___boxed(lean_object* v_cls_1615_, lean_object* v_msg_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(v_cls_1615_, v_msg_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5(lean_object* v_00_u03b1_1631_, lean_object* v_x_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(v_x_1632_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1647_, lean_object* v_x_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5(v_00_u03b1_1647_, v_x_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4(lean_object* v_oldTraces_1663_, lean_object* v_data_1664_, lean_object* v_ref_1665_, lean_object* v_msg_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(v_oldTraces_1663_, v_data_1664_, v_ref_1665_, v_msg_1666_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___boxed(lean_object** _args){
lean_object* v_oldTraces_1681_ = _args[0];
lean_object* v_data_1682_ = _args[1];
lean_object* v_ref_1683_ = _args[2];
lean_object* v_msg_1684_ = _args[3];
lean_object* v___y_1685_ = _args[4];
lean_object* v___y_1686_ = _args[5];
lean_object* v___y_1687_ = _args[6];
lean_object* v___y_1688_ = _args[7];
lean_object* v___y_1689_ = _args[8];
lean_object* v___y_1690_ = _args[9];
lean_object* v___y_1691_ = _args[10];
lean_object* v___y_1692_ = _args[11];
lean_object* v___y_1693_ = _args[12];
lean_object* v___y_1694_ = _args[13];
lean_object* v___y_1695_ = _args[14];
lean_object* v___y_1696_ = _args[15];
lean_object* v___y_1697_ = _args[16];
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4(v_oldTraces_1681_, v_data_1682_, v_ref_1683_, v_msg_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
return v_res_1698_;
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
