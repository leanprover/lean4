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
lean_object* v___x_218_; lean_object* v_env_219_; lean_object* v___x_220_; lean_object* v_toCold_221_; lean_object* v_mctx_222_; lean_object* v_lctx_223_; lean_object* v_options_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_218_ = lean_st_ref_get(v___y_216_);
v_env_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc_ref(v_env_219_);
lean_dec(v___x_218_);
v___x_220_ = lean_st_ref_get(v___y_214_);
v_toCold_221_ = lean_ctor_get(v___y_215_, 0);
v_mctx_222_ = lean_ctor_get(v___x_220_, 0);
lean_inc_ref(v_mctx_222_);
lean_dec(v___x_220_);
v_lctx_223_ = lean_ctor_get(v___y_213_, 2);
v_options_224_ = lean_ctor_get(v_toCold_221_, 2);
lean_inc_ref(v_options_224_);
lean_inc_ref(v_lctx_223_);
v___x_225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_225_, 0, v_env_219_);
lean_ctor_set(v___x_225_, 1, v_mctx_222_);
lean_ctor_set(v___x_225_, 2, v_lctx_223_);
lean_ctor_set(v___x_225_, 3, v_options_224_);
v___x_226_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v_msgData_212_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5___boxed(lean_object* v_msgData_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msgData_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(lean_object* v_msg_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_ref_241_; lean_object* v___x_242_; lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_251_; 
v_ref_241_ = lean_ctor_get(v___y_238_, 2);
v___x_242_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_251_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
lean_inc(v_ref_241_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_ref_241_);
lean_ctor_set(v___x_247_, 1, v_a_243_);
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 1);
lean_ctor_set(v___x_245_, 0, v___x_247_);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg___boxed(lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
return v_res_258_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(lean_object* v_a_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
uint8_t v___x_261_; 
v___x_261_ = 0;
return v___x_261_;
}
else
{
lean_object* v_key_262_; lean_object* v_tail_263_; lean_object* v_type_264_; lean_object* v_type_265_; uint8_t v___x_266_; 
v_key_262_ = lean_ctor_get(v_x_260_, 0);
v_tail_263_ = lean_ctor_get(v_x_260_, 2);
v_type_264_ = lean_ctor_get(v_key_262_, 1);
v_type_265_ = lean_ctor_get(v_a_259_, 1);
v___x_266_ = lean_expr_eqv(v_type_264_, v_type_265_);
if (v___x_266_ == 0)
{
v_x_260_ = v_tail_263_;
goto _start;
}
else
{
return v___x_266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg___boxed(lean_object* v_a_268_, lean_object* v_x_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_268_, v_x_269_);
lean_dec(v_x_269_);
lean_dec_ref(v_a_268_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
if (lean_obj_tag(v_x_273_) == 0)
{
return v_x_272_;
}
else
{
lean_object* v_key_274_; lean_object* v_value_275_; lean_object* v_tail_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_300_; 
v_key_274_ = lean_ctor_get(v_x_273_, 0);
v_value_275_ = lean_ctor_get(v_x_273_, 1);
v_tail_276_ = lean_ctor_get(v_x_273_, 2);
v_isSharedCheck_300_ = !lean_is_exclusive(v_x_273_);
if (v_isSharedCheck_300_ == 0)
{
v___x_278_ = v_x_273_;
v_isShared_279_ = v_isSharedCheck_300_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_tail_276_);
lean_inc(v_value_275_);
lean_inc(v_key_274_);
lean_dec(v_x_273_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_300_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v_type_280_; lean_object* v___x_281_; uint64_t v___x_282_; uint64_t v___x_283_; uint64_t v___x_284_; uint64_t v_fold_285_; uint64_t v___x_286_; uint64_t v___x_287_; uint64_t v___x_288_; size_t v___x_289_; size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v_type_280_ = lean_ctor_get(v_key_274_, 1);
v___x_281_ = lean_array_get_size(v_x_272_);
v___x_282_ = l_Lean_Expr_hash(v_type_280_);
v___x_283_ = 32ULL;
v___x_284_ = lean_uint64_shift_right(v___x_282_, v___x_283_);
v_fold_285_ = lean_uint64_xor(v___x_282_, v___x_284_);
v___x_286_ = 16ULL;
v___x_287_ = lean_uint64_shift_right(v_fold_285_, v___x_286_);
v___x_288_ = lean_uint64_xor(v_fold_285_, v___x_287_);
v___x_289_ = lean_uint64_to_usize(v___x_288_);
v___x_290_ = lean_usize_of_nat(v___x_281_);
v___x_291_ = ((size_t)1ULL);
v___x_292_ = lean_usize_sub(v___x_290_, v___x_291_);
v___x_293_ = lean_usize_land(v___x_289_, v___x_292_);
v___x_294_ = lean_array_uget_borrowed(v_x_272_, v___x_293_);
lean_inc(v___x_294_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 2, v___x_294_);
v___x_296_ = v___x_278_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_key_274_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_value_275_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v___x_294_);
v___x_296_ = v_reuseFailAlloc_299_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; 
v___x_297_ = lean_array_uset(v_x_272_, v___x_293_, v___x_296_);
v_x_272_ = v___x_297_;
v_x_273_ = v_tail_276_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(lean_object* v_i_301_, lean_object* v_source_302_, lean_object* v_target_303_){
_start:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = lean_array_get_size(v_source_302_);
v___x_305_ = lean_nat_dec_lt(v_i_301_, v___x_304_);
if (v___x_305_ == 0)
{
lean_dec_ref(v_source_302_);
lean_dec(v_i_301_);
return v_target_303_;
}
else
{
lean_object* v_es_306_; lean_object* v___x_307_; lean_object* v_source_308_; lean_object* v_target_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_es_306_ = lean_array_fget(v_source_302_, v_i_301_);
v___x_307_ = lean_box(0);
v_source_308_ = lean_array_fset(v_source_302_, v_i_301_, v___x_307_);
v_target_309_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(v_target_303_, v_es_306_);
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = lean_nat_add(v_i_301_, v___x_310_);
lean_dec(v_i_301_);
v_i_301_ = v___x_311_;
v_source_302_ = v_source_308_;
v_target_303_ = v_target_309_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(lean_object* v_data_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v_nbuckets_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_314_ = lean_array_get_size(v_data_313_);
v___x_315_ = lean_unsigned_to_nat(2u);
v_nbuckets_316_ = lean_nat_mul(v___x_314_, v___x_315_);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_box(0);
v___x_319_ = lean_mk_array(v_nbuckets_316_, v___x_318_);
v___x_320_ = lean_array_propagate_mark(v_data_313_, v___x_319_);
v___x_321_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v___x_317_, v_data_313_, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(lean_object* v_m_322_, lean_object* v_a_323_, lean_object* v_b_324_){
_start:
{
lean_object* v_size_325_; lean_object* v_buckets_326_; lean_object* v_type_327_; lean_object* v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; uint64_t v_fold_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; size_t v___x_336_; size_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; lean_object* v_bkt_341_; uint8_t v___x_342_; 
v_size_325_ = lean_ctor_get(v_m_322_, 0);
v_buckets_326_ = lean_ctor_get(v_m_322_, 1);
v_type_327_ = lean_ctor_get(v_a_323_, 1);
v___x_328_ = lean_array_get_size(v_buckets_326_);
v___x_329_ = l_Lean_Expr_hash(v_type_327_);
v___x_330_ = 32ULL;
v___x_331_ = lean_uint64_shift_right(v___x_329_, v___x_330_);
v_fold_332_ = lean_uint64_xor(v___x_329_, v___x_331_);
v___x_333_ = 16ULL;
v___x_334_ = lean_uint64_shift_right(v_fold_332_, v___x_333_);
v___x_335_ = lean_uint64_xor(v_fold_332_, v___x_334_);
v___x_336_ = lean_uint64_to_usize(v___x_335_);
v___x_337_ = lean_usize_of_nat(v___x_328_);
v___x_338_ = ((size_t)1ULL);
v___x_339_ = lean_usize_sub(v___x_337_, v___x_338_);
v___x_340_ = lean_usize_land(v___x_336_, v___x_339_);
v_bkt_341_ = lean_array_uget_borrowed(v_buckets_326_, v___x_340_);
v___x_342_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_323_, v_bkt_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_363_; 
lean_inc_ref(v_buckets_326_);
lean_inc(v_size_325_);
v_isSharedCheck_363_ = !lean_is_exclusive(v_m_322_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; lean_object* v_unused_365_; 
v_unused_364_ = lean_ctor_get(v_m_322_, 1);
lean_dec(v_unused_364_);
v_unused_365_ = lean_ctor_get(v_m_322_, 0);
lean_dec(v_unused_365_);
v___x_344_ = v_m_322_;
v_isShared_345_ = v_isSharedCheck_363_;
goto v_resetjp_343_;
}
else
{
lean_dec(v_m_322_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_363_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v_size_x27_347_; lean_object* v___x_348_; lean_object* v_buckets_x27_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_346_ = lean_unsigned_to_nat(1u);
v_size_x27_347_ = lean_nat_add(v_size_325_, v___x_346_);
lean_dec(v_size_325_);
lean_inc(v_bkt_341_);
v___x_348_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_348_, 0, v_a_323_);
lean_ctor_set(v___x_348_, 1, v_b_324_);
lean_ctor_set(v___x_348_, 2, v_bkt_341_);
v_buckets_x27_349_ = lean_array_uset(v_buckets_326_, v___x_340_, v___x_348_);
v___x_350_ = lean_unsigned_to_nat(4u);
v___x_351_ = lean_nat_mul(v_size_x27_347_, v___x_350_);
v___x_352_ = lean_unsigned_to_nat(3u);
v___x_353_ = lean_nat_div(v___x_351_, v___x_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_array_get_size(v_buckets_x27_349_);
v___x_355_ = lean_nat_dec_le(v___x_353_, v___x_354_);
lean_dec(v___x_353_);
if (v___x_355_ == 0)
{
lean_object* v_val_356_; lean_object* v___x_358_; 
v_val_356_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_buckets_x27_349_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v_val_356_);
lean_ctor_set(v___x_344_, 0, v_size_x27_347_);
v___x_358_ = v___x_344_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_size_x27_347_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_val_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
else
{
lean_object* v___x_361_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v_buckets_x27_349_);
lean_ctor_set(v___x_344_, 0, v_size_x27_347_);
v___x_361_ = v___x_344_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_size_x27_347_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_buckets_x27_349_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_dec(v_b_324_);
lean_dec_ref(v_a_323_);
return v_m_322_;
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_box(0);
v___x_370_ = lean_unsigned_to_nat(16u);
v___x_371_ = lean_mk_array(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4(void){
_start:
{
lean_object* v___x_375_; lean_object* v_sats_376_; lean_object* v___x_377_; 
v___x_375_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3);
v_sats_376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0));
v___x_377_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_377_, 0, v_sats_376_);
lean_ctor_set(v___x_377_, 1, v___x_375_);
lean_ctor_set(v___x_377_, 2, v___x_375_);
lean_ctor_set(v___x_377_, 3, v___x_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(lean_object* v_as_378_, size_t v_sz_379_, size_t v_i_380_, lean_object* v_b_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_a_395_; uint8_t v___x_399_; 
v___x_399_ = lean_usize_dec_lt(v_i_380_, v_sz_379_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; 
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v_b_381_);
return v___x_400_;
}
else
{
lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v_a_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_fst_401_ = lean_ctor_get(v_b_381_, 0);
lean_inc(v_fst_401_);
v_snd_402_ = lean_ctor_get(v_b_381_, 1);
lean_inc(v_snd_402_);
lean_dec_ref(v_b_381_);
v_a_403_ = lean_array_uget_borrowed(v_as_378_, v_i_380_);
v___x_404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1));
v___x_405_ = l_Lean_Core_checkSystem(v___x_404_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec_ref_known(v___x_405_, 1);
lean_inc(v_a_403_);
v___x_406_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed), 14, 1);
lean_closure_set(v___x_406_, 0, v_a_403_);
v___x_407_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4);
v___x_408_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v___x_406_, v___x_407_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v_fst_410_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
v_fst_410_ = lean_ctor_get(v_a_409_, 0);
if (lean_obj_tag(v_fst_410_) == 1)
{
lean_object* v_snd_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_421_; 
lean_inc_ref(v_fst_410_);
v_snd_411_ = lean_ctor_get(v_a_409_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_a_409_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v_a_409_, 0);
lean_dec(v_unused_422_);
v___x_413_ = v_a_409_;
v_isShared_414_ = v_isSharedCheck_421_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_snd_411_);
lean_dec(v_a_409_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_421_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v_val_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v_val_415_ = lean_ctor_get(v_fst_410_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v_fst_410_, 1);
v___x_416_ = l_Array_append___redArg(v_fst_401_, v_snd_411_);
lean_dec(v_snd_411_);
v___x_417_ = lean_array_push(v___x_416_, v_val_415_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v_snd_402_);
lean_ctor_set(v___x_413_, 0, v___x_417_);
v___x_419_ = v___x_413_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_snd_402_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
v_a_395_ = v___x_419_;
goto v___jp_394_;
}
}
}
else
{
lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_431_; 
v_isSharedCheck_431_ = !lean_is_exclusive(v_a_409_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; lean_object* v_unused_433_; 
v_unused_432_ = lean_ctor_get(v_a_409_, 1);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_a_409_, 0);
lean_dec(v_unused_433_);
v___x_424_ = v_a_409_;
v_isShared_425_ = v_isSharedCheck_431_;
goto v_resetjp_423_;
}
else
{
lean_dec(v_a_409_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_431_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_426_ = lean_box(0);
lean_inc(v_a_403_);
v___x_427_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_snd_402_, v_a_403_, v___x_426_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v___x_427_);
lean_ctor_set(v___x_424_, 0, v_fst_401_);
v___x_429_ = v___x_424_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_fst_401_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
v_a_395_ = v___x_429_;
goto v___jp_394_;
}
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec(v_snd_402_);
lean_dec(v_fst_401_);
v_a_434_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_408_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_408_);
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
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
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
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec(v_snd_402_);
lean_dec(v_fst_401_);
v_a_442_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_405_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_405_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
v___jp_394_:
{
size_t v___x_396_; size_t v___x_397_; 
v___x_396_ = ((size_t)1ULL);
v___x_397_ = lean_usize_add(v_i_380_, v___x_396_);
v_i_380_ = v___x_397_;
v_b_381_ = v_a_395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___boxed(lean_object* v_as_450_, lean_object* v_sz_451_, lean_object* v_i_452_, lean_object* v_b_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
size_t v_sz_boxed_466_; size_t v_i_boxed_467_; lean_object* v_res_468_; 
v_sz_boxed_466_ = lean_unbox_usize(v_sz_451_);
lean_dec(v_sz_451_);
v_i_boxed_467_ = lean_unbox_usize(v_i_452_);
lean_dec(v_i_452_);
v_res_468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v_as_450_, v_sz_boxed_466_, v_i_boxed_467_, v_b_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec_ref(v_as_450_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(lean_object* v_a_469_, lean_object* v_b_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_array_478_; lean_object* v_start_479_; lean_object* v_stop_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_495_; 
v_array_478_ = lean_ctor_get(v_a_469_, 0);
v_start_479_ = lean_ctor_get(v_a_469_, 1);
v_stop_480_ = lean_ctor_get(v_a_469_, 2);
v_isSharedCheck_495_ = !lean_is_exclusive(v_a_469_);
if (v_isSharedCheck_495_ == 0)
{
v___x_482_ = v_a_469_;
v_isShared_483_ = v_isSharedCheck_495_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_stop_480_);
lean_inc(v_start_479_);
lean_inc(v_array_478_);
lean_dec(v_a_469_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_495_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
uint8_t v___x_484_; 
v___x_484_ = lean_nat_dec_lt(v_start_479_, v_stop_480_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; 
lean_del_object(v___x_482_);
lean_dec(v_stop_480_);
lean_dec(v_start_479_);
lean_dec_ref(v_array_478_);
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v_b_470_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_start_479_, v___x_486_);
lean_inc_ref(v_array_478_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v___x_487_);
v___x_489_ = v___x_482_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_array_478_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_stop_480_);
v___x_489_ = v_reuseFailAlloc_494_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_array_fget(v_array_478_, v_start_479_);
lean_dec(v_start_479_);
lean_dec_ref(v_array_478_);
v___x_491_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_b_470_, v___x_490_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v_a_469_ = v___x_489_;
v_b_470_ = v_a_492_;
goto _start;
}
else
{
lean_dec_ref(v___x_489_);
return v___x_491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg___boxed(lean_object* v_a_496_, lean_object* v_b_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_496_, v_b_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v_res_505_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1));
v___x_510_ = l_Lean_MessageData_ofFormat(v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(lean_object* v_sats_511_, lean_object* v_unusedHypotheses_512_, lean_object* v___x_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_hypotheses_526_; lean_object* v___x_527_; size_t v_sz_528_; size_t v___x_529_; lean_object* v___x_530_; 
v_hypotheses_526_ = lean_ctor_get(v___y_514_, 0);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v_sats_511_);
lean_ctor_set(v___x_527_, 1, v_unusedHypotheses_512_);
v_sz_528_ = lean_array_size(v_hypotheses_526_);
v___x_529_ = ((size_t)0ULL);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v_hypotheses_526_, v_sz_528_, v___x_529_, v___x_527_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v_fst_532_; lean_object* v_snd_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_575_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_530_, 1);
v_fst_532_ = lean_ctor_get(v_a_531_, 0);
v_snd_533_ = lean_ctor_get(v_a_531_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_a_531_);
if (v_isSharedCheck_575_ == 0)
{
v___x_535_ = v_a_531_;
v_isShared_536_ = v_isSharedCheck_575_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_snd_533_);
lean_inc(v_fst_532_);
lean_dec(v_a_531_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_575_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = lean_array_get_size(v_fst_532_);
v___x_538_ = lean_nat_dec_eq(v___x_537_, v___x_513_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_539_ = lean_array_fget(v_fst_532_, v___x_513_);
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = l_Array_toSubarray___redArg(v_fst_532_, v___x_540_, v___x_537_);
v___x_542_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v___x_541_, v___x_539_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_564_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_564_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_564_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_564_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v_bvExpr_547_; lean_object* v_satAtAtoms_548_; lean_object* v_expr_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_563_; 
v_bvExpr_547_ = lean_ctor_get(v_a_543_, 0);
v_satAtAtoms_548_ = lean_ctor_get(v_a_543_, 1);
v_expr_549_ = lean_ctor_get(v_a_543_, 2);
v_isSharedCheck_563_ = !lean_is_exclusive(v_a_543_);
if (v_isSharedCheck_563_ == 0)
{
v___x_551_ = v_a_543_;
v_isShared_552_ = v_isSharedCheck_563_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_expr_549_);
lean_inc(v_satAtAtoms_548_);
lean_inc(v_bvExpr_547_);
lean_dec(v_a_543_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_563_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = l_Lean_ShareCommon_shareCommon___redArg(v_bvExpr_547_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_satAtAtoms_548_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_expr_549_);
v___x_555_ = v_reuseFailAlloc_562_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_557_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_555_);
v___x_557_ = v___x_535_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_snd_533_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_557_);
v___x_559_ = v___x_545_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_del_object(v___x_535_);
lean_dec(v_snd_533_);
v_a_565_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_542_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_542_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
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
else
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_del_object(v___x_535_);
lean_dec(v_snd_533_);
lean_dec(v_fst_532_);
v___x_573_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2);
v___x_574_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v___x_573_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
return v___x_574_;
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
v_a_576_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_530_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_530_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed(lean_object* v_sats_584_, lean_object* v_unusedHypotheses_585_, lean_object* v___x_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(v_sats_584_, v_unusedHypotheses_585_, v___x_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___x_586_);
return v_res_599_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_box(0);
v___x_601_ = lean_unsigned_to_nat(16u);
v___x_602_ = lean_mk_array(v___x_601_, v___x_600_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_unusedHypotheses_605_; 
v___x_603_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0);
v___x_604_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_unusedHypotheses_605_, 0, v___x_604_);
lean_ctor_set(v_unusedHypotheses_605_, 1, v___x_603_);
return v_unusedHypotheses_605_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2(void){
_start:
{
lean_object* v___x_606_; lean_object* v_unusedHypotheses_607_; lean_object* v_sats_608_; lean_object* v___f_609_; 
v___x_606_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_607_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1);
v_sats_608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0));
v___f_609_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed), 15, 3);
lean_closure_set(v___f_609_, 0, v_sats_608_);
lean_closure_set(v___f_609_, 1, v_unusedHypotheses_607_);
lean_closure_set(v___f_609_, 2, v___x_606_);
return v___f_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV(lean_object* v_g_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___f_623_; lean_object* v___x_624_; 
v___f_623_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2);
v___x_624_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_g_610_, v___f_623_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___boxed(lean_object* v_g_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0(lean_object* v_00_u03b2_639_, lean_object* v_m_640_, lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_m_640_, v_a_641_, v_b_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(lean_object* v_inst_644_, lean_object* v_R_645_, lean_object* v_a_646_, lean_object* v_b_647_, lean_object* v_c_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_646_, v_b_647_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___boxed(lean_object** _args){
lean_object* v_inst_662_ = _args[0];
lean_object* v_R_663_ = _args[1];
lean_object* v_a_664_ = _args[2];
lean_object* v_b_665_ = _args[3];
lean_object* v_c_666_ = _args[4];
lean_object* v___y_667_ = _args[5];
lean_object* v___y_668_ = _args[6];
lean_object* v___y_669_ = _args[7];
lean_object* v___y_670_ = _args[8];
lean_object* v___y_671_ = _args[9];
lean_object* v___y_672_ = _args[10];
lean_object* v___y_673_ = _args[11];
lean_object* v___y_674_ = _args[12];
lean_object* v___y_675_ = _args[13];
lean_object* v___y_676_ = _args[14];
lean_object* v___y_677_ = _args[15];
lean_object* v___y_678_ = _args[16];
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(v_inst_662_, v_R_663_, v_a_664_, v_b_665_, v_c_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(lean_object* v_00_u03b1_680_, lean_object* v_msg_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_681_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___boxed(lean_object* v_00_u03b1_695_, lean_object* v_msg_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(v_00_u03b1_695_, v_msg_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
return v_res_709_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(lean_object* v_00_u03b2_710_, lean_object* v_a_711_, lean_object* v_x_712_){
_start:
{
uint8_t v___x_713_; 
v___x_713_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_711_, v_x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___boxed(lean_object* v_00_u03b2_714_, lean_object* v_a_715_, lean_object* v_x_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(v_00_u03b2_714_, v_a_715_, v_x_716_);
lean_dec(v_x_716_);
lean_dec_ref(v_a_715_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1(lean_object* v_00_u03b2_719_, lean_object* v_data_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_data_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_722_, lean_object* v_i_723_, lean_object* v_source_724_, lean_object* v_target_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v_i_723_, v_source_724_, v_target_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_727_, lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(v_x_728_, v_x_729_);
return v___x_730_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_unsigned_to_nat(32u);
v___x_732_ = lean_mk_empty_array_with_capacity(v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_734_ = ((size_t)5ULL);
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = lean_unsigned_to_nat(32u);
v___x_737_ = lean_mk_empty_array_with_capacity(v___x_736_);
v___x_738_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__0);
v___x_739_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v___x_737_);
lean_ctor_set(v___x_739_, 2, v___x_735_);
lean_ctor_set(v___x_739_, 3, v___x_735_);
lean_ctor_set_usize(v___x_739_, 4, v___x_734_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(lean_object* v___y_740_){
_start:
{
lean_object* v___x_742_; lean_object* v_traceState_743_; lean_object* v_traces_744_; lean_object* v___x_745_; lean_object* v_traceState_746_; lean_object* v_env_747_; lean_object* v_nextMacroScope_748_; lean_object* v_ngen_749_; lean_object* v_auxDeclNGen_750_; lean_object* v_cache_751_; lean_object* v_recordedDeps_752_; lean_object* v_messages_753_; lean_object* v_infoState_754_; lean_object* v_snapshotTasks_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_774_; 
v___x_742_ = lean_st_ref_get(v___y_740_);
v_traceState_743_ = lean_ctor_get(v___x_742_, 4);
lean_inc_ref(v_traceState_743_);
lean_dec(v___x_742_);
v_traces_744_ = lean_ctor_get(v_traceState_743_, 0);
lean_inc_ref(v_traces_744_);
lean_dec_ref(v_traceState_743_);
v___x_745_ = lean_st_ref_take(v___y_740_);
v_traceState_746_ = lean_ctor_get(v___x_745_, 4);
v_env_747_ = lean_ctor_get(v___x_745_, 0);
v_nextMacroScope_748_ = lean_ctor_get(v___x_745_, 1);
v_ngen_749_ = lean_ctor_get(v___x_745_, 2);
v_auxDeclNGen_750_ = lean_ctor_get(v___x_745_, 3);
v_cache_751_ = lean_ctor_get(v___x_745_, 5);
v_recordedDeps_752_ = lean_ctor_get(v___x_745_, 6);
v_messages_753_ = lean_ctor_get(v___x_745_, 7);
v_infoState_754_ = lean_ctor_get(v___x_745_, 8);
v_snapshotTasks_755_ = lean_ctor_get(v___x_745_, 9);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_774_ == 0)
{
v___x_757_ = v___x_745_;
v_isShared_758_ = v_isSharedCheck_774_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_snapshotTasks_755_);
lean_inc(v_infoState_754_);
lean_inc(v_messages_753_);
lean_inc(v_recordedDeps_752_);
lean_inc(v_cache_751_);
lean_inc(v_traceState_746_);
lean_inc(v_auxDeclNGen_750_);
lean_inc(v_ngen_749_);
lean_inc(v_nextMacroScope_748_);
lean_inc(v_env_747_);
lean_dec(v___x_745_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_774_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
uint64_t v_tid_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_772_; 
v_tid_759_ = lean_ctor_get_uint64(v_traceState_746_, sizeof(void*)*1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_traceState_746_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; 
v_unused_773_ = lean_ctor_get(v_traceState_746_, 0);
lean_dec(v_unused_773_);
v___x_761_ = v_traceState_746_;
v_isShared_762_ = v_isSharedCheck_772_;
goto v_resetjp_760_;
}
else
{
lean_dec(v_traceState_746_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_772_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___closed__1);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_763_);
v___x_765_ = v___x_761_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_763_);
lean_ctor_set_uint64(v_reuseFailAlloc_771_, sizeof(void*)*1, v_tid_759_);
v___x_765_ = v_reuseFailAlloc_771_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 4, v___x_765_);
v___x_767_ = v___x_757_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_env_747_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_nextMacroScope_748_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_ngen_749_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_auxDeclNGen_750_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_770_, 5, v_cache_751_);
lean_ctor_set(v_reuseFailAlloc_770_, 6, v_recordedDeps_752_);
lean_ctor_set(v_reuseFailAlloc_770_, 7, v_messages_753_);
lean_ctor_set(v_reuseFailAlloc_770_, 8, v_infoState_754_);
lean_ctor_set(v_reuseFailAlloc_770_, 9, v_snapshotTasks_755_);
v___x_767_ = v_reuseFailAlloc_770_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_st_ref_put(v___y_740_, v___x_767_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v_traces_744_);
return v___x_769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___boxed(lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v___y_775_);
lean_dec(v___y_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v___y_789_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___boxed(lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
return v_res_805_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(lean_object* v_opts_806_, lean_object* v_opt_807_){
_start:
{
lean_object* v_name_808_; lean_object* v_defValue_809_; lean_object* v_map_810_; lean_object* v___x_811_; 
v_name_808_ = lean_ctor_get(v_opt_807_, 0);
v_defValue_809_ = lean_ctor_get(v_opt_807_, 1);
v_map_810_ = lean_ctor_get(v_opts_806_, 0);
v___x_811_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_810_, v_name_808_);
if (lean_obj_tag(v___x_811_) == 0)
{
uint8_t v___x_812_; 
v___x_812_ = lean_unbox(v_defValue_809_);
return v___x_812_;
}
else
{
lean_object* v_val_813_; 
v_val_813_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_val_813_);
lean_dec_ref_known(v___x_811_, 1);
if (lean_obj_tag(v_val_813_) == 1)
{
uint8_t v_v_814_; 
v_v_814_ = lean_ctor_get_uint8(v_val_813_, 0);
lean_dec_ref_known(v_val_813_, 0);
return v_v_814_;
}
else
{
uint8_t v___x_815_; 
lean_dec(v_val_813_);
v___x_815_ = lean_unbox(v_defValue_809_);
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___boxed(lean_object* v_opts_816_, lean_object* v_opt_817_){
_start:
{
uint8_t v_res_818_; lean_object* v_r_819_; 
v_res_818_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_opts_816_, v_opt_817_);
lean_dec_ref(v_opt_817_);
lean_dec_ref(v_opts_816_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0(lean_object* v_x_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; 
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v___y_824_);
lean_inc(v___y_823_);
lean_inc_ref(v___y_822_);
lean_inc(v___y_821_);
v___x_834_ = lean_apply_13(v_x_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, lean_box(0));
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0___boxed(lean_object* v_x_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0(v_x_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(lean_object* v_mvarId_850_, lean_object* v_x_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v___f_865_; lean_object* v___x_866_; 
lean_inc(v___y_859_);
lean_inc_ref(v___y_858_);
lean_inc(v___y_857_);
lean_inc_ref(v___y_856_);
lean_inc(v___y_855_);
lean_inc(v___y_854_);
lean_inc_ref(v___y_853_);
lean_inc(v___y_852_);
v___f_865_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_865_, 0, v_x_851_);
lean_closure_set(v___f_865_, 1, v___y_852_);
lean_closure_set(v___f_865_, 2, v___y_853_);
lean_closure_set(v___f_865_, 3, v___y_854_);
lean_closure_set(v___f_865_, 4, v___y_855_);
lean_closure_set(v___f_865_, 5, v___y_856_);
lean_closure_set(v___f_865_, 6, v___y_857_);
lean_closure_set(v___f_865_, 7, v___y_858_);
lean_closure_set(v___f_865_, 8, v___y_859_);
v___x_866_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_850_, v___f_865_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
if (lean_obj_tag(v___x_866_) == 0)
{
return v___x_866_;
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___boxed(lean_object* v_mvarId_875_, lean_object* v_x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(v_mvarId_875_, v_x_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(lean_object* v_00_u03b1_891_, lean_object* v_mvarId_892_, lean_object* v_x_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(v_mvarId_892_, v_x_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___boxed(lean_object* v_00_u03b1_908_, lean_object* v_mvarId_909_, lean_object* v_x_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_00_u03b1_908_, v_mvarId_909_, v_x_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
return v_res_924_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1));
v___x_929_ = l_Lean_MessageData_ofFormat(v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(lean_object* v_x_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed(lean_object* v_x_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(v_x_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v_x_946_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7(lean_object* v_opts_961_, lean_object* v_opt_962_){
_start:
{
lean_object* v_name_963_; lean_object* v_defValue_964_; lean_object* v_map_965_; lean_object* v___x_966_; 
v_name_963_ = lean_ctor_get(v_opt_962_, 0);
v_defValue_964_ = lean_ctor_get(v_opt_962_, 1);
v_map_965_ = lean_ctor_get(v_opts_961_, 0);
v___x_966_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_965_, v_name_963_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_inc(v_defValue_964_);
return v_defValue_964_;
}
else
{
lean_object* v_val_967_; 
v_val_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_val_967_);
lean_dec_ref_known(v___x_966_, 1);
if (lean_obj_tag(v_val_967_) == 3)
{
lean_object* v_v_968_; 
v_v_968_ = lean_ctor_get(v_val_967_, 0);
lean_inc(v_v_968_);
lean_dec_ref_known(v_val_967_, 1);
return v_v_968_;
}
else
{
lean_dec(v_val_967_);
lean_inc(v_defValue_964_);
return v_defValue_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7___boxed(lean_object* v_opts_969_, lean_object* v_opt_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7(v_opts_969_, v_opt_970_);
lean_dec_ref(v_opt_970_);
lean_dec_ref(v_opts_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(lean_object* v_x_972_){
_start:
{
if (lean_obj_tag(v_x_972_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
v_a_974_ = lean_ctor_get(v_x_972_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v_x_972_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v_x_972_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set_tag(v___x_976_, 1);
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
v_a_982_ = lean_ctor_get(v_x_972_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v_x_972_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v_x_972_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set_tag(v___x_984_, 0);
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg___boxed(lean_object* v_x_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(v_x_990_);
return v_res_992_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6(lean_object* v_e_993_){
_start:
{
if (lean_obj_tag(v_e_993_) == 0)
{
uint8_t v___x_994_; 
v___x_994_ = 2;
return v___x_994_;
}
else
{
uint8_t v___x_995_; 
v___x_995_ = 0;
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6___boxed(lean_object* v_e_996_){
_start:
{
uint8_t v_res_997_; lean_object* v_r_998_; 
v_res_997_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6(v_e_996_);
lean_dec_ref(v_e_996_);
v_r_998_ = lean_box(v_res_997_);
return v_r_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6(size_t v_sz_999_, size_t v_i_1000_, lean_object* v_bs_1001_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_usize_dec_lt(v_i_1000_, v_sz_999_);
if (v___x_1002_ == 0)
{
return v_bs_1001_;
}
else
{
lean_object* v_v_1003_; lean_object* v_msg_1004_; lean_object* v___x_1005_; lean_object* v_bs_x27_1006_; size_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; 
v_v_1003_ = lean_array_uget_borrowed(v_bs_1001_, v_i_1000_);
v_msg_1004_ = lean_ctor_get(v_v_1003_, 1);
lean_inc_ref(v_msg_1004_);
v___x_1005_ = lean_unsigned_to_nat(0u);
v_bs_x27_1006_ = lean_array_uset(v_bs_1001_, v_i_1000_, v___x_1005_);
v___x_1007_ = ((size_t)1ULL);
v___x_1008_ = lean_usize_add(v_i_1000_, v___x_1007_);
v___x_1009_ = lean_array_uset(v_bs_x27_1006_, v_i_1000_, v_msg_1004_);
v_i_1000_ = v___x_1008_;
v_bs_1001_ = v___x_1009_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6___boxed(lean_object* v_sz_1011_, lean_object* v_i_1012_, lean_object* v_bs_1013_){
_start:
{
size_t v_sz_boxed_1014_; size_t v_i_boxed_1015_; lean_object* v_res_1016_; 
v_sz_boxed_1014_ = lean_unbox_usize(v_sz_1011_);
lean_dec(v_sz_1011_);
v_i_boxed_1015_ = lean_unbox_usize(v_i_1012_);
lean_dec(v_i_1012_);
v_res_1016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6(v_sz_boxed_1014_, v_i_boxed_1015_, v_bs_1013_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(lean_object* v_oldTraces_1017_, lean_object* v_data_1018_, lean_object* v_ref_1019_, lean_object* v_msg_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_toCold_1026_; lean_object* v_currRecDepth_1027_; lean_object* v_ref_1028_; uint16_t v_optionFlags_1029_; uint8_t v_suppressElabErrors_1030_; uint8_t v_isRecordingDeps_1031_; lean_object* v_ref_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_traceState_1035_; lean_object* v_traces_1036_; lean_object* v___x_1037_; size_t v_sz_1038_; size_t v___x_1039_; lean_object* v___x_1040_; lean_object* v_msg_1041_; lean_object* v___x_1042_; lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1081_; 
v_toCold_1026_ = lean_ctor_get(v___y_1023_, 0);
v_currRecDepth_1027_ = lean_ctor_get(v___y_1023_, 1);
v_ref_1028_ = lean_ctor_get(v___y_1023_, 2);
v_optionFlags_1029_ = lean_ctor_get_uint16(v___y_1023_, sizeof(void*)*3);
v_suppressElabErrors_1030_ = lean_ctor_get_uint8(v___y_1023_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1031_ = lean_ctor_get_uint8(v___y_1023_, sizeof(void*)*3 + 3);
v_ref_1032_ = l_Lean_replaceRef(v_ref_1019_, v_ref_1028_);
lean_inc(v_currRecDepth_1027_);
lean_inc_ref(v_toCold_1026_);
v___x_1033_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1033_, 0, v_toCold_1026_);
lean_ctor_set(v___x_1033_, 1, v_currRecDepth_1027_);
lean_ctor_set(v___x_1033_, 2, v_ref_1032_);
lean_ctor_set_uint16(v___x_1033_, sizeof(void*)*3, v_optionFlags_1029_);
lean_ctor_set_uint8(v___x_1033_, sizeof(void*)*3 + 2, v_suppressElabErrors_1030_);
lean_ctor_set_uint8(v___x_1033_, sizeof(void*)*3 + 3, v_isRecordingDeps_1031_);
v___x_1034_ = lean_st_ref_get(v___y_1024_);
v_traceState_1035_ = lean_ctor_get(v___x_1034_, 4);
lean_inc_ref(v_traceState_1035_);
lean_dec(v___x_1034_);
v_traces_1036_ = lean_ctor_get(v_traceState_1035_, 0);
lean_inc_ref(v_traces_1036_);
lean_dec_ref(v_traceState_1035_);
v___x_1037_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1036_);
lean_dec_ref(v_traces_1036_);
v_sz_1038_ = lean_array_size(v___x_1037_);
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4_spec__6(v_sz_1038_, v___x_1039_, v___x_1037_);
v_msg_1041_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1041_, 0, v_data_1018_);
lean_ctor_set(v_msg_1041_, 1, v_msg_1020_);
lean_ctor_set(v_msg_1041_, 2, v___x_1040_);
v___x_1042_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_1041_, v___y_1021_, v___y_1022_, v___x_1033_, v___y_1024_);
lean_dec_ref_known(v___x_1033_, 3);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1081_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1081_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v_traceState_1048_; lean_object* v_env_1049_; lean_object* v_nextMacroScope_1050_; lean_object* v_ngen_1051_; lean_object* v_auxDeclNGen_1052_; lean_object* v_cache_1053_; lean_object* v_recordedDeps_1054_; lean_object* v_messages_1055_; lean_object* v_infoState_1056_; lean_object* v_snapshotTasks_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1080_; 
v___x_1047_ = lean_st_ref_take(v___y_1024_);
v_traceState_1048_ = lean_ctor_get(v___x_1047_, 4);
v_env_1049_ = lean_ctor_get(v___x_1047_, 0);
v_nextMacroScope_1050_ = lean_ctor_get(v___x_1047_, 1);
v_ngen_1051_ = lean_ctor_get(v___x_1047_, 2);
v_auxDeclNGen_1052_ = lean_ctor_get(v___x_1047_, 3);
v_cache_1053_ = lean_ctor_get(v___x_1047_, 5);
v_recordedDeps_1054_ = lean_ctor_get(v___x_1047_, 6);
v_messages_1055_ = lean_ctor_get(v___x_1047_, 7);
v_infoState_1056_ = lean_ctor_get(v___x_1047_, 8);
v_snapshotTasks_1057_ = lean_ctor_get(v___x_1047_, 9);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1059_ = v___x_1047_;
v_isShared_1060_ = v_isSharedCheck_1080_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_snapshotTasks_1057_);
lean_inc(v_infoState_1056_);
lean_inc(v_messages_1055_);
lean_inc(v_recordedDeps_1054_);
lean_inc(v_cache_1053_);
lean_inc(v_traceState_1048_);
lean_inc(v_auxDeclNGen_1052_);
lean_inc(v_ngen_1051_);
lean_inc(v_nextMacroScope_1050_);
lean_inc(v_env_1049_);
lean_dec(v___x_1047_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1080_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
uint64_t v_tid_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1078_; 
v_tid_1061_ = lean_ctor_get_uint64(v_traceState_1048_, sizeof(void*)*1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_traceState_1048_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v_traceState_1048_, 0);
lean_dec(v_unused_1079_);
v___x_1063_ = v_traceState_1048_;
v_isShared_1064_ = v_isSharedCheck_1078_;
goto v_resetjp_1062_;
}
else
{
lean_dec(v_traceState_1048_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1078_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_ref_1019_);
lean_ctor_set(v___x_1066_, 1, v_a_1043_);
v___x_1067_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1017_, v___x_1066_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1067_);
v___x_1069_ = v___x_1063_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1067_);
lean_ctor_set_uint64(v_reuseFailAlloc_1077_, sizeof(void*)*1, v_tid_1061_);
v___x_1069_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1071_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 4, v___x_1069_);
v___x_1071_ = v___x_1059_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_env_1049_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_nextMacroScope_1050_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_ngen_1051_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v_auxDeclNGen_1052_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1076_, 5, v_cache_1053_);
lean_ctor_set(v_reuseFailAlloc_1076_, 6, v_recordedDeps_1054_);
lean_ctor_set(v_reuseFailAlloc_1076_, 7, v_messages_1055_);
lean_ctor_set(v_reuseFailAlloc_1076_, 8, v_infoState_1056_);
lean_ctor_set(v_reuseFailAlloc_1076_, 9, v_snapshotTasks_1057_);
v___x_1071_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = lean_st_ref_put(v___y_1024_, v___x_1071_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1065_);
v___x_1074_ = v___x_1045_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1065_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg___boxed(lean_object* v_oldTraces_1082_, lean_object* v_data_1083_, lean_object* v_ref_1084_, lean_object* v_msg_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(v_oldTraces_1082_, v_data_1083_, v_ref_1084_, v_msg_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
return v_res_1091_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1092_; double v___x_1093_; 
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_float_of_nat(v___x_1092_);
return v___x_1093_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__1));
v___x_1096_ = l_Lean_stringToMessageData(v___x_1095_);
return v___x_1096_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1097_; double v___x_1098_; 
v___x_1097_ = lean_unsigned_to_nat(1000u);
v___x_1098_ = lean_float_of_nat(v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(lean_object* v_cls_1099_, uint8_t v_collapsed_1100_, lean_object* v_tag_1101_, lean_object* v_opts_1102_, uint8_t v_clsEnabled_1103_, lean_object* v_oldTraces_1104_, lean_object* v_msg_1105_, lean_object* v_resStartStop_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_fst_1120_; lean_object* v_snd_1121_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v_data_1125_; lean_object* v_fst_1136_; lean_object* v_snd_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; lean_object* v___y_1141_; lean_object* v_a_1142_; uint8_t v___y_1157_; double v___y_1189_; 
v_fst_1120_ = lean_ctor_get(v_resStartStop_1106_, 0);
lean_inc(v_fst_1120_);
v_snd_1121_ = lean_ctor_get(v_resStartStop_1106_, 1);
lean_inc(v_snd_1121_);
lean_dec_ref(v_resStartStop_1106_);
v_fst_1136_ = lean_ctor_get(v_snd_1121_, 0);
lean_inc(v_fst_1136_);
v_snd_1137_ = lean_ctor_get(v_snd_1121_, 1);
lean_inc(v_snd_1137_);
lean_dec(v_snd_1121_);
v___x_1138_ = l_Lean_trace_profiler;
v___x_1139_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_opts_1102_, v___x_1138_);
if (v___x_1139_ == 0)
{
v___y_1157_ = v___x_1139_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1195_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_opts_1102_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; double v___x_1198_; double v___x_1199_; double v___x_1200_; 
v___x_1196_ = l_Lean_trace_profiler_threshold;
v___x_1197_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7(v_opts_1102_, v___x_1196_);
v___x_1198_ = lean_float_of_nat(v___x_1197_);
v___x_1199_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3);
v___x_1200_ = lean_float_div(v___x_1198_, v___x_1199_);
v___y_1189_ = v___x_1200_;
goto v___jp_1188_;
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; double v___x_1203_; 
v___x_1201_ = l_Lean_trace_profiler_threshold;
v___x_1202_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__7(v_opts_1102_, v___x_1201_);
v___x_1203_ = lean_float_of_nat(v___x_1202_);
v___y_1189_ = v___x_1203_;
goto v___jp_1188_;
}
}
v___jp_1122_:
{
lean_object* v___x_1126_; 
lean_inc(v___y_1124_);
v___x_1126_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(v_oldTraces_1104_, v_data_1125_, v___y_1124_, v___y_1123_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1127_; 
lean_dec_ref_known(v___x_1126_, 1);
v___x_1127_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(v_fst_1120_);
return v___x_1127_;
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v_fst_1120_);
v_a_1128_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1126_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1126_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
v___jp_1140_:
{
uint8_t v_result_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; double v___x_1146_; lean_object* v_data_1147_; 
v_result_1143_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__6(v_fst_1120_);
v___x_1144_ = lean_box(v_result_1143_);
v___x_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
v___x_1146_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0);
lean_inc_ref(v_tag_1101_);
lean_inc_ref(v___x_1145_);
lean_inc(v_cls_1099_);
v_data_1147_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1147_, 0, v_cls_1099_);
lean_ctor_set(v_data_1147_, 1, v___x_1145_);
lean_ctor_set(v_data_1147_, 2, v_tag_1101_);
lean_ctor_set_float(v_data_1147_, sizeof(void*)*3, v___x_1146_);
lean_ctor_set_float(v_data_1147_, sizeof(void*)*3 + 8, v___x_1146_);
lean_ctor_set_uint8(v_data_1147_, sizeof(void*)*3 + 16, v_collapsed_1100_);
if (v___x_1139_ == 0)
{
lean_dec_ref_known(v___x_1145_, 1);
lean_dec(v_snd_1137_);
lean_dec(v_fst_1136_);
lean_dec_ref(v_tag_1101_);
lean_dec(v_cls_1099_);
v___y_1123_ = v_a_1142_;
v___y_1124_ = v___y_1141_;
v_data_1125_ = v_data_1147_;
goto v___jp_1122_;
}
else
{
lean_object* v_data_1148_; double v___x_1149_; double v___x_1150_; 
lean_dec_ref_known(v_data_1147_, 3);
v_data_1148_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1148_, 0, v_cls_1099_);
lean_ctor_set(v_data_1148_, 1, v___x_1145_);
lean_ctor_set(v_data_1148_, 2, v_tag_1101_);
v___x_1149_ = lean_unbox_float(v_fst_1136_);
lean_dec(v_fst_1136_);
lean_ctor_set_float(v_data_1148_, sizeof(void*)*3, v___x_1149_);
v___x_1150_ = lean_unbox_float(v_snd_1137_);
lean_dec(v_snd_1137_);
lean_ctor_set_float(v_data_1148_, sizeof(void*)*3 + 8, v___x_1150_);
lean_ctor_set_uint8(v_data_1148_, sizeof(void*)*3 + 16, v_collapsed_1100_);
v___y_1123_ = v_a_1142_;
v___y_1124_ = v___y_1141_;
v_data_1125_ = v_data_1148_;
goto v___jp_1122_;
}
}
v___jp_1151_:
{
lean_object* v_ref_1152_; lean_object* v___x_1153_; 
v_ref_1152_ = lean_ctor_get(v___y_1117_, 2);
lean_inc(v___y_1118_);
lean_inc_ref(v___y_1117_);
lean_inc(v___y_1116_);
lean_inc_ref(v___y_1115_);
lean_inc(v___y_1114_);
lean_inc_ref(v___y_1113_);
lean_inc(v___y_1112_);
lean_inc_ref(v___y_1111_);
lean_inc(v___y_1110_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
lean_inc(v___y_1107_);
lean_inc(v_fst_1120_);
v___x_1153_ = lean_apply_14(v_msg_1105_, v_fst_1120_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, lean_box(0));
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1153_, 1);
v___y_1141_ = v_ref_1152_;
v_a_1142_ = v_a_1154_;
goto v___jp_1140_;
}
else
{
lean_object* v___x_1155_; 
lean_dec_ref_known(v___x_1153_, 1);
v___x_1155_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2);
v___y_1141_ = v_ref_1152_;
v_a_1142_ = v___x_1155_;
goto v___jp_1140_;
}
}
v___jp_1156_:
{
if (v_clsEnabled_1103_ == 0)
{
if (v___y_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v_traceState_1159_; lean_object* v_env_1160_; lean_object* v_nextMacroScope_1161_; lean_object* v_ngen_1162_; lean_object* v_auxDeclNGen_1163_; lean_object* v_cache_1164_; lean_object* v_recordedDeps_1165_; lean_object* v_messages_1166_; lean_object* v_infoState_1167_; lean_object* v_snapshotTasks_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_snd_1137_);
lean_dec(v_fst_1136_);
lean_dec_ref(v_msg_1105_);
lean_dec_ref(v_tag_1101_);
lean_dec(v_cls_1099_);
v___x_1158_ = lean_st_ref_take(v___y_1118_);
v_traceState_1159_ = lean_ctor_get(v___x_1158_, 4);
v_env_1160_ = lean_ctor_get(v___x_1158_, 0);
v_nextMacroScope_1161_ = lean_ctor_get(v___x_1158_, 1);
v_ngen_1162_ = lean_ctor_get(v___x_1158_, 2);
v_auxDeclNGen_1163_ = lean_ctor_get(v___x_1158_, 3);
v_cache_1164_ = lean_ctor_get(v___x_1158_, 5);
v_recordedDeps_1165_ = lean_ctor_get(v___x_1158_, 6);
v_messages_1166_ = lean_ctor_get(v___x_1158_, 7);
v_infoState_1167_ = lean_ctor_get(v___x_1158_, 8);
v_snapshotTasks_1168_ = lean_ctor_get(v___x_1158_, 9);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1170_ = v___x_1158_;
v_isShared_1171_ = v_isSharedCheck_1187_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_snapshotTasks_1168_);
lean_inc(v_infoState_1167_);
lean_inc(v_messages_1166_);
lean_inc(v_recordedDeps_1165_);
lean_inc(v_cache_1164_);
lean_inc(v_traceState_1159_);
lean_inc(v_auxDeclNGen_1163_);
lean_inc(v_ngen_1162_);
lean_inc(v_nextMacroScope_1161_);
lean_inc(v_env_1160_);
lean_dec(v___x_1158_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1187_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
uint64_t v_tid_1172_; lean_object* v_traces_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1186_; 
v_tid_1172_ = lean_ctor_get_uint64(v_traceState_1159_, sizeof(void*)*1);
v_traces_1173_ = lean_ctor_get(v_traceState_1159_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_traceState_1159_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1175_ = v_traceState_1159_;
v_isShared_1176_ = v_isSharedCheck_1186_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_traces_1173_);
lean_dec(v_traceState_1159_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1186_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1104_, v_traces_1173_);
lean_dec_ref(v_traces_1173_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1177_);
v___x_1179_ = v___x_1175_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1177_);
lean_ctor_set_uint64(v_reuseFailAlloc_1185_, sizeof(void*)*1, v_tid_1172_);
v___x_1179_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1181_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 4, v___x_1179_);
v___x_1181_ = v___x_1170_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_env_1160_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_nextMacroScope_1161_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_ngen_1162_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_auxDeclNGen_1163_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1184_, 5, v_cache_1164_);
lean_ctor_set(v_reuseFailAlloc_1184_, 6, v_recordedDeps_1165_);
lean_ctor_set(v_reuseFailAlloc_1184_, 7, v_messages_1166_);
lean_ctor_set(v_reuseFailAlloc_1184_, 8, v_infoState_1167_);
lean_ctor_set(v_reuseFailAlloc_1184_, 9, v_snapshotTasks_1168_);
v___x_1181_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_st_ref_put(v___y_1118_, v___x_1181_);
v___x_1183_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(v_fst_1120_);
return v___x_1183_;
}
}
}
}
}
else
{
goto v___jp_1151_;
}
}
else
{
goto v___jp_1151_;
}
}
v___jp_1188_:
{
double v___x_1190_; double v___x_1191_; double v___x_1192_; uint8_t v___x_1193_; 
v___x_1190_ = lean_unbox_float(v_snd_1137_);
v___x_1191_ = lean_unbox_float(v_fst_1136_);
v___x_1192_ = lean_float_sub(v___x_1190_, v___x_1191_);
v___x_1193_ = lean_float_decLt(v___y_1189_, v___x_1192_);
v___y_1157_ = v___x_1193_;
goto v___jp_1156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___boxed(lean_object** _args){
lean_object* v_cls_1204_ = _args[0];
lean_object* v_collapsed_1205_ = _args[1];
lean_object* v_tag_1206_ = _args[2];
lean_object* v_opts_1207_ = _args[3];
lean_object* v_clsEnabled_1208_ = _args[4];
lean_object* v_oldTraces_1209_ = _args[5];
lean_object* v_msg_1210_ = _args[6];
lean_object* v_resStartStop_1211_ = _args[7];
lean_object* v___y_1212_ = _args[8];
lean_object* v___y_1213_ = _args[9];
lean_object* v___y_1214_ = _args[10];
lean_object* v___y_1215_ = _args[11];
lean_object* v___y_1216_ = _args[12];
lean_object* v___y_1217_ = _args[13];
lean_object* v___y_1218_ = _args[14];
lean_object* v___y_1219_ = _args[15];
lean_object* v___y_1220_ = _args[16];
lean_object* v___y_1221_ = _args[17];
lean_object* v___y_1222_ = _args[18];
lean_object* v___y_1223_ = _args[19];
lean_object* v___y_1224_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_1225_; uint8_t v_clsEnabled_boxed_1226_; lean_object* v_res_1227_; 
v_collapsed_boxed_1225_ = lean_unbox(v_collapsed_1205_);
v_clsEnabled_boxed_1226_ = lean_unbox(v_clsEnabled_1208_);
v_res_1227_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_cls_1204_, v_collapsed_boxed_1225_, v_tag_1206_, v_opts_1207_, v_clsEnabled_boxed_1226_, v_oldTraces_1209_, v_msg_1210_, v_resStartStop_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v_opts_1207_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(lean_object* v_cls_1231_, lean_object* v_msg_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_ref_1238_; lean_object* v___x_1239_; lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1285_; 
v_ref_1238_ = lean_ctor_get(v___y_1235_, 2);
v___x_1239_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1285_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1285_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v_traceState_1245_; lean_object* v_env_1246_; lean_object* v_nextMacroScope_1247_; lean_object* v_ngen_1248_; lean_object* v_auxDeclNGen_1249_; lean_object* v_cache_1250_; lean_object* v_recordedDeps_1251_; lean_object* v_messages_1252_; lean_object* v_infoState_1253_; lean_object* v_snapshotTasks_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1284_; 
v___x_1244_ = lean_st_ref_take(v___y_1236_);
v_traceState_1245_ = lean_ctor_get(v___x_1244_, 4);
v_env_1246_ = lean_ctor_get(v___x_1244_, 0);
v_nextMacroScope_1247_ = lean_ctor_get(v___x_1244_, 1);
v_ngen_1248_ = lean_ctor_get(v___x_1244_, 2);
v_auxDeclNGen_1249_ = lean_ctor_get(v___x_1244_, 3);
v_cache_1250_ = lean_ctor_get(v___x_1244_, 5);
v_recordedDeps_1251_ = lean_ctor_get(v___x_1244_, 6);
v_messages_1252_ = lean_ctor_get(v___x_1244_, 7);
v_infoState_1253_ = lean_ctor_get(v___x_1244_, 8);
v_snapshotTasks_1254_ = lean_ctor_get(v___x_1244_, 9);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1256_ = v___x_1244_;
v_isShared_1257_ = v_isSharedCheck_1284_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_snapshotTasks_1254_);
lean_inc(v_infoState_1253_);
lean_inc(v_messages_1252_);
lean_inc(v_recordedDeps_1251_);
lean_inc(v_cache_1250_);
lean_inc(v_traceState_1245_);
lean_inc(v_auxDeclNGen_1249_);
lean_inc(v_ngen_1248_);
lean_inc(v_nextMacroScope_1247_);
lean_inc(v_env_1246_);
lean_dec(v___x_1244_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1284_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
uint64_t v_tid_1258_; lean_object* v_traces_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1283_; 
v_tid_1258_ = lean_ctor_get_uint64(v_traceState_1245_, sizeof(void*)*1);
v_traces_1259_ = lean_ctor_get(v_traceState_1245_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_traceState_1245_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1261_ = v_traceState_1245_;
v_isShared_1262_ = v_isSharedCheck_1283_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_traces_1259_);
lean_dec(v_traceState_1245_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1283_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; double v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0);
v___x_1266_ = 0;
v___x_1267_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__0));
v___x_1268_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1268_, 0, v_cls_1231_);
lean_ctor_set(v___x_1268_, 1, v___x_1264_);
lean_ctor_set(v___x_1268_, 2, v___x_1267_);
lean_ctor_set_float(v___x_1268_, sizeof(void*)*3, v___x_1265_);
lean_ctor_set_float(v___x_1268_, sizeof(void*)*3 + 8, v___x_1265_);
lean_ctor_set_uint8(v___x_1268_, sizeof(void*)*3 + 16, v___x_1266_);
v___x_1269_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__1));
v___x_1270_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set(v___x_1270_, 1, v_a_1240_);
lean_ctor_set(v___x_1270_, 2, v___x_1269_);
lean_inc(v_ref_1238_);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v_ref_1238_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = l_Lean_PersistentArray_push___redArg(v_traces_1259_, v___x_1271_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v___x_1272_);
v___x_1274_ = v___x_1261_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1272_);
lean_ctor_set_uint64(v_reuseFailAlloc_1282_, sizeof(void*)*1, v_tid_1258_);
v___x_1274_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1276_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 4, v___x_1274_);
v___x_1276_ = v___x_1256_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_env_1246_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_nextMacroScope_1247_);
lean_ctor_set(v_reuseFailAlloc_1281_, 2, v_ngen_1248_);
lean_ctor_set(v_reuseFailAlloc_1281_, 3, v_auxDeclNGen_1249_);
lean_ctor_set(v_reuseFailAlloc_1281_, 4, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1281_, 5, v_cache_1250_);
lean_ctor_set(v_reuseFailAlloc_1281_, 6, v_recordedDeps_1251_);
lean_ctor_set(v_reuseFailAlloc_1281_, 7, v_messages_1252_);
lean_ctor_set(v_reuseFailAlloc_1281_, 8, v_infoState_1253_);
lean_ctor_set(v_reuseFailAlloc_1281_, 9, v_snapshotTasks_1254_);
v___x_1276_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = lean_st_ref_put(v___y_1236_, v___x_1276_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1263_);
v___x_1279_ = v___x_1242_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1263_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___boxed(lean_object* v_cls_1286_, lean_object* v_msg_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(v_cls_1286_, v_msg_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(lean_object* v_x_1301_){
_start:
{
switch(lean_obj_tag(v_x_1301_))
{
case 0:
{
lean_object* v_a_1302_; lean_object* v___x_1303_; 
v_a_1302_ = lean_ctor_get(v_x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v_x_1301_, 1);
v___x_1303_ = l_Std_Tactic_BVDecide_BVPred_toString(v_a_1302_);
return v___x_1303_;
}
case 1:
{
uint8_t v_a_1304_; 
v_a_1304_ = lean_ctor_get_uint8(v_x_1301_, 0);
lean_dec_ref_known(v_x_1301_, 0);
if (v_a_1304_ == 0)
{
lean_object* v___x_1305_; 
v___x_1305_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__0));
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; 
v___x_1306_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__1));
return v___x_1306_;
}
}
case 2:
{
lean_object* v_a_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_a_1307_ = lean_ctor_get(v_x_1301_, 0);
lean_inc_ref(v_a_1307_);
lean_dec_ref_known(v_x_1301_, 1);
v___x_1308_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__2));
v___x_1309_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1307_);
v___x_1310_ = lean_string_append(v___x_1308_, v___x_1309_);
lean_dec_ref(v___x_1309_);
return v___x_1310_;
}
case 3:
{
uint8_t v_a_1311_; lean_object* v_a_1312_; lean_object* v_a_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_a_1311_ = lean_ctor_get_uint8(v_x_1301_, sizeof(void*)*2);
v_a_1312_ = lean_ctor_get(v_x_1301_, 0);
lean_inc_ref(v_a_1312_);
v_a_1313_ = lean_ctor_get(v_x_1301_, 1);
lean_inc_ref(v_a_1313_);
lean_dec_ref_known(v_x_1301_, 2);
v___x_1314_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__3));
v___x_1315_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1312_);
v___x_1316_ = lean_string_append(v___x_1314_, v___x_1315_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__4));
v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
v___x_1319_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_1311_);
v___x_1320_ = lean_string_append(v___x_1318_, v___x_1319_);
lean_dec_ref(v___x_1319_);
v___x_1321_ = lean_string_append(v___x_1320_, v___x_1317_);
v___x_1322_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1313_);
v___x_1323_ = lean_string_append(v___x_1321_, v___x_1322_);
lean_dec_ref(v___x_1322_);
v___x_1324_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__5));
v___x_1325_ = lean_string_append(v___x_1323_, v___x_1324_);
return v___x_1325_;
}
default: 
{
lean_object* v_a_1326_; lean_object* v_a_1327_; lean_object* v_a_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_a_1326_ = lean_ctor_get(v_x_1301_, 0);
lean_inc_ref(v_a_1326_);
v_a_1327_ = lean_ctor_get(v_x_1301_, 1);
lean_inc_ref(v_a_1327_);
v_a_1328_ = lean_ctor_get(v_x_1301_, 2);
lean_inc_ref(v_a_1328_);
lean_dec_ref_known(v_x_1301_, 3);
v___x_1329_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__6));
v___x_1330_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1326_);
v___x_1331_ = lean_string_append(v___x_1329_, v___x_1330_);
lean_dec_ref(v___x_1330_);
v___x_1332_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__4));
v___x_1333_ = lean_string_append(v___x_1331_, v___x_1332_);
v___x_1334_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1327_);
v___x_1335_ = lean_string_append(v___x_1333_, v___x_1334_);
lean_dec_ref(v___x_1334_);
v___x_1336_ = lean_string_append(v___x_1335_, v___x_1332_);
v___x_1337_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_a_1328_);
v___x_1338_ = lean_string_append(v___x_1336_, v___x_1337_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___closed__5));
v___x_1340_ = lean_string_append(v___x_1338_, v___x_1339_);
return v___x_1340_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2));
v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
return v___x_1346_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1347_; double v___x_1348_; 
v___x_1347_ = lean_unsigned_to_nat(1000000000u);
v___x_1348_ = lean_float_of_nat(v___x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(lean_object* v_unsatProver_1349_, lean_object* v_g_1350_, lean_object* v_cls_1351_, uint8_t v___x_1352_, lean_object* v___x_1353_, lean_object* v___f_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_toCold_1368_; lean_object* v_options_1369_; lean_object* v_inheritedTraceOptions_1370_; uint8_t v_hasTrace_1371_; lean_object* v___y_1373_; 
v_toCold_1368_ = lean_ctor_get(v___y_1365_, 0);
v_options_1369_ = lean_ctor_get(v_toCold_1368_, 2);
v_inheritedTraceOptions_1370_ = lean_ctor_get(v_toCold_1368_, 11);
v_hasTrace_1371_ = lean_ctor_get_uint8(v_options_1369_, sizeof(void*)*1);
if (v_hasTrace_1371_ == 0)
{
lean_object* v___x_1406_; 
lean_dec_ref(v___f_1354_);
lean_dec_ref(v___x_1353_);
lean_inc(v_g_1350_);
v___x_1406_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1350_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
v___y_1373_ = v___x_1406_;
goto v___jp_1372_;
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v_a_1413_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v_a_1428_; 
v___x_1407_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1));
lean_inc(v_cls_1351_);
v___x_1408_ = l_Lean_Name_append(v___x_1407_, v_cls_1351_);
v___x_1409_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1370_, v_options_1369_, v___x_1408_);
lean_dec(v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = l_Lean_trace_profiler;
v___x_1479_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_options_1369_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
lean_dec_ref(v___f_1354_);
lean_dec_ref(v___x_1353_);
lean_inc(v_g_1350_);
v___x_1480_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1350_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
v___y_1373_ = v___x_1480_;
goto v___jp_1372_;
}
else
{
goto v___jp_1437_;
}
}
else
{
goto v___jp_1437_;
}
v___jp_1410_:
{
lean_object* v___x_1414_; double v___x_1415_; double v___x_1416_; double v___x_1417_; double v___x_1418_; double v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1414_ = lean_io_mono_nanos_now();
v___x_1415_ = lean_float_of_nat(v___y_1412_);
v___x_1416_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4);
v___x_1417_ = lean_float_div(v___x_1415_, v___x_1416_);
v___x_1418_ = lean_float_of_nat(v___x_1414_);
v___x_1419_ = lean_float_div(v___x_1418_, v___x_1416_);
v___x_1420_ = lean_box_float(v___x_1417_);
v___x_1421_ = lean_box_float(v___x_1419_);
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1423_, 0, v_a_1413_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
lean_inc(v_cls_1351_);
v___x_1424_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_cls_1351_, v___x_1352_, v___x_1353_, v_options_1369_, v___x_1409_, v___y_1411_, v___f_1354_, v___x_1423_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
v___y_1373_ = v___x_1424_;
goto v___jp_1372_;
}
v___jp_1425_:
{
lean_object* v___x_1429_; double v___x_1430_; double v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1429_ = lean_io_get_num_heartbeats();
v___x_1430_ = lean_float_of_nat(v___y_1427_);
v___x_1431_ = lean_float_of_nat(v___x_1429_);
v___x_1432_ = lean_box_float(v___x_1430_);
v___x_1433_ = lean_box_float(v___x_1431_);
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_a_1428_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
lean_inc(v_cls_1351_);
v___x_1436_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_cls_1351_, v___x_1352_, v___x_1353_, v_options_1369_, v___x_1409_, v___y_1426_, v___f_1354_, v___x_1435_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
v___y_1373_ = v___x_1436_;
goto v___jp_1372_;
}
v___jp_1437_:
{
lean_object* v___x_1438_; lean_object* v_a_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1438_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v___y_1366_);
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref(v___x_1438_);
v___x_1440_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1441_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_options_1369_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_io_mono_nanos_now();
lean_inc(v_g_1350_);
v___x_1443_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1350_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1443_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1443_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
lean_ctor_set_tag(v___x_1446_, 1);
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
v___y_1411_ = v_a_1439_;
v___y_1412_ = v___x_1442_;
v_a_1413_ = v___x_1449_;
goto v___jp_1410_;
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
v_a_1452_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1443_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1443_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set_tag(v___x_1454_, 0);
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
v___y_1411_ = v_a_1439_;
v___y_1412_ = v___x_1442_;
v_a_1413_ = v___x_1457_;
goto v___jp_1410_;
}
}
}
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_io_get_num_heartbeats();
lean_inc(v_g_1350_);
v___x_1461_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1350_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set_tag(v___x_1464_, 1);
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
v___y_1426_ = v_a_1439_;
v___y_1427_ = v___x_1460_;
v_a_1428_ = v___x_1467_;
goto v___jp_1425_;
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
v_a_1470_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1461_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1461_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set_tag(v___x_1472_, 0);
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
v___y_1426_ = v_a_1439_;
v___y_1427_ = v___x_1460_;
v_a_1428_ = v___x_1475_;
goto v___jp_1425_;
}
}
}
}
}
}
v___jp_1372_:
{
if (lean_obj_tag(v___y_1373_) == 0)
{
if (v_hasTrace_1371_ == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1375_; 
lean_dec(v_cls_1351_);
v_a_1374_ = lean_ctor_get(v___y_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___y_1373_, 1);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
lean_inc(v___y_1362_);
lean_inc_ref(v___y_1361_);
lean_inc(v___y_1360_);
lean_inc_ref(v___y_1359_);
lean_inc(v___y_1358_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
v___x_1375_ = lean_apply_15(v_unsatProver_1349_, v_g_1350_, v_a_1374_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, lean_box(0));
return v___x_1375_;
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v_a_1376_ = lean_ctor_get(v___y_1373_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___y_1373_, 1);
v___x_1377_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1));
lean_inc(v_cls_1351_);
v___x_1378_ = l_Lean_Name_append(v___x_1377_, v_cls_1351_);
v___x_1379_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1370_, v_options_1369_, v___x_1378_);
lean_dec(v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
lean_dec(v_cls_1351_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
lean_inc(v___y_1362_);
lean_inc_ref(v___y_1361_);
lean_inc(v___y_1360_);
lean_inc_ref(v___y_1359_);
lean_inc(v___y_1358_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
v___x_1380_ = lean_apply_15(v_unsatProver_1349_, v_g_1350_, v_a_1376_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, lean_box(0));
return v___x_1380_;
}
else
{
lean_object* v_satExpr_1381_; lean_object* v_bvExpr_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_satExpr_1381_ = lean_ctor_get(v_a_1376_, 0);
v_bvExpr_1382_ = lean_ctor_get(v_satExpr_1381_, 0);
v___x_1383_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3);
lean_inc_ref(v_bvExpr_1382_);
v___x_1384_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_bvExpr_1382_);
v___x_1385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
v___x_1386_ = l_Lean_MessageData_ofFormat(v___x_1385_);
v___x_1387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1383_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(v_cls_1351_, v___x_1387_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v___x_1389_; 
lean_dec_ref_known(v___x_1388_, 1);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
lean_inc(v___y_1362_);
lean_inc_ref(v___y_1361_);
lean_inc(v___y_1360_);
lean_inc_ref(v___y_1359_);
lean_inc(v___y_1358_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
v___x_1389_ = lean_apply_15(v_unsatProver_1349_, v_g_1350_, v_a_1376_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, lean_box(0));
return v___x_1389_;
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_a_1376_);
lean_dec(v_g_1350_);
lean_dec_ref(v_unsatProver_1349_);
v_a_1390_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1388_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1388_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec(v_cls_1351_);
lean_dec(v_g_1350_);
lean_dec_ref(v_unsatProver_1349_);
v_a_1398_ = lean_ctor_get(v___y_1373_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___y_1373_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___y_1373_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___y_1373_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_unsatProver_1481_ = _args[0];
lean_object* v_g_1482_ = _args[1];
lean_object* v_cls_1483_ = _args[2];
lean_object* v___x_1484_ = _args[3];
lean_object* v___x_1485_ = _args[4];
lean_object* v___f_1486_ = _args[5];
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
lean_object* v___y_1498_ = _args[17];
lean_object* v___y_1499_ = _args[18];
_start:
{
uint8_t v___x_64518__boxed_1500_; lean_object* v_res_1501_; 
v___x_64518__boxed_1500_ = lean_unbox(v___x_1484_);
v_res_1501_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(v_unsatProver_1481_, v_g_1482_, v_cls_1483_, v___x_64518__boxed_1500_, v___x_1485_, v___f_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(lean_object* v_g_1510_, lean_object* v_unsatProver_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v___f_1524_; lean_object* v_cls_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___f_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___f_1524_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0));
v_cls_1525_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4));
v___x_1526_ = 1;
v___x_1527_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg___closed__0));
v___x_1528_ = lean_box(v___x_1526_);
lean_inc(v_g_1510_);
v___f_1529_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed), 19, 6);
lean_closure_set(v___f_1529_, 0, v_unsatProver_1511_);
lean_closure_set(v___f_1529_, 1, v_g_1510_);
lean_closure_set(v___f_1529_, 2, v_cls_1525_);
lean_closure_set(v___f_1529_, 3, v___x_1528_);
lean_closure_set(v___f_1529_, 4, v___x_1527_);
lean_closure_set(v___f_1529_, 5, v___f_1524_);
v___x_1530_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___boxed), 16, 3);
lean_closure_set(v___x_1530_, 0, lean_box(0));
lean_closure_set(v___x_1530_, 1, v_g_1510_);
lean_closure_set(v___x_1530_, 2, v___f_1529_);
v___x_1531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4);
v___x_1532_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v___x_1530_, v___x_1531_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1541_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1535_ = v___x_1532_;
v_isShared_1536_ = v_isSharedCheck_1541_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1532_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1541_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v_fst_1537_; lean_object* v___x_1539_; 
v_fst_1537_ = lean_ctor_get(v_a_1533_, 0);
lean_inc(v_fst_1537_);
lean_dec(v_a_1533_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v_fst_1537_);
v___x_1539_ = v___x_1535_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_fst_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
v_a_1542_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1532_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1532_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___boxed(lean_object* v_g_1550_, lean_object* v_unsatProver_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1550_, v_unsatProver_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(lean_object* v_00_u03b1_1565_, lean_object* v_g_1566_, lean_object* v_unsatProver_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1566_, v_unsatProver_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed(lean_object* v_00_u03b1_1581_, lean_object* v_g_1582_, lean_object* v_unsatProver_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(v_00_u03b1_1581_, v_g_1582_, v_unsatProver_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(lean_object* v_cls_1597_, lean_object* v_msg_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___redArg(v_cls_1597_, v_msg_1598_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___boxed(lean_object* v_cls_1613_, lean_object* v_msg_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(v_cls_1613_, v_msg_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5(lean_object* v_00_u03b1_1629_, lean_object* v_x_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___redArg(v_x_1630_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1645_, lean_object* v_x_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__5(v_00_u03b1_1645_, v_x_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4(lean_object* v_oldTraces_1661_, lean_object* v_data_1662_, lean_object* v_ref_1663_, lean_object* v_msg_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___redArg(v_oldTraces_1661_, v_data_1662_, v_ref_1663_, v_msg_1664_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4___boxed(lean_object** _args){
lean_object* v_oldTraces_1679_ = _args[0];
lean_object* v_data_1680_ = _args[1];
lean_object* v_ref_1681_ = _args[2];
lean_object* v_msg_1682_ = _args[3];
lean_object* v___y_1683_ = _args[4];
lean_object* v___y_1684_ = _args[5];
lean_object* v___y_1685_ = _args[6];
lean_object* v___y_1686_ = _args[7];
lean_object* v___y_1687_ = _args[8];
lean_object* v___y_1688_ = _args[9];
lean_object* v___y_1689_ = _args[10];
lean_object* v___y_1690_ = _args[11];
lean_object* v___y_1691_ = _args[12];
lean_object* v___y_1692_ = _args[13];
lean_object* v___y_1693_ = _args[14];
lean_object* v___y_1694_ = _args[15];
lean_object* v___y_1695_ = _args[16];
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4_spec__4(v_oldTraces_1679_, v_data_1680_, v_ref_1681_, v_msg_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
return v_res_1696_;
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
