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
double lean_float_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_Gate_toString(uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ShareCommon_shareCommon___redArg(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 443, .m_capacity = 443, .m_length = 442, .m_data = "None of the hypotheses are in the supported BitVec fragment after applying preprocessing.\nThere are three potential reasons for this:\n1. If you are using custom BitVec constructs simplify them to built-in ones.\n2. If your problem is using only built-in ones it might currently be out of reach.\n   Consider expressing it in terms of different operations that are better supported.\n3. The original goal was reduced to False and is thus invalid."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Reflecting goal into BVLogicalExpr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__3_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__5_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "(if "};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Reflected bv logical expression: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; 
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_11_ = lean_apply_9(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0___boxed(lean_object* v_x_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0(v_x_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(lean_object* v_mvarId_23_, lean_object* v_x_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___f_34_; lean_object* v___x_35_; 
lean_inc(v___y_28_);
lean_inc_ref(v___y_27_);
lean_inc(v___y_26_);
lean_inc_ref(v___y_25_);
v___f_34_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_34_, 0, v_x_24_);
lean_closure_set(v___f_34_, 1, v___y_25_);
lean_closure_set(v___f_34_, 2, v___y_26_);
lean_closure_set(v___f_34_, 3, v___y_27_);
lean_closure_set(v___f_34_, 4, v___y_28_);
v___x_35_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_23_, v___f_34_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
if (lean_obj_tag(v___x_35_) == 0)
{
return v___x_35_;
}
else
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
v_a_36_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_35_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_35_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___boxed(lean_object* v_mvarId_44_, lean_object* v_x_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_mvarId_44_, v_x_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(lean_object* v_00_u03b1_56_, lean_object* v_mvarId_57_, lean_object* v_x_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_mvarId_57_, v_x_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___boxed(lean_object* v_00_u03b1_69_, lean_object* v_mvarId_70_, lean_object* v_x_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(v_00_u03b1_69_, v_mvarId_70_, v_x_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(lean_object* v_msgData_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; lean_object* v_env_89_; lean_object* v___x_90_; lean_object* v_toCold_91_; lean_object* v_mctx_92_; lean_object* v_lctx_93_; lean_object* v_options_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_88_ = lean_st_ref_get(v___y_86_);
v_env_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc_ref(v_env_89_);
lean_dec(v___x_88_);
v___x_90_ = lean_st_ref_get(v___y_84_);
v_toCold_91_ = lean_ctor_get(v___y_85_, 0);
v_mctx_92_ = lean_ctor_get(v___x_90_, 0);
lean_inc_ref(v_mctx_92_);
lean_dec(v___x_90_);
v_lctx_93_ = lean_ctor_get(v___y_83_, 2);
v_options_94_ = lean_ctor_get(v_toCold_91_, 2);
lean_inc_ref(v_options_94_);
lean_inc_ref(v_lctx_93_);
v___x_95_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_95_, 0, v_env_89_);
lean_ctor_set(v___x_95_, 1, v_mctx_92_);
lean_ctor_set(v___x_95_, 2, v_lctx_93_);
lean_ctor_set(v___x_95_, 3, v_options_94_);
v___x_96_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v_msgData_82_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5___boxed(lean_object* v_msgData_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msgData_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(lean_object* v_msg_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_ref_111_; lean_object* v___x_112_; lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_121_; 
v_ref_111_ = lean_ctor_get(v___y_108_, 2);
v___x_112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_121_ == 0)
{
v___x_115_ = v___x_112_;
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; lean_object* v___x_119_; 
lean_inc(v_ref_111_);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v_ref_111_);
lean_ctor_set(v___x_117_, 1, v_a_113_);
if (v_isShared_116_ == 0)
{
lean_ctor_set_tag(v___x_115_, 1);
lean_ctor_set(v___x_115_, 0, v___x_117_);
v___x_119_ = v___x_115_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg___boxed(lean_object* v_msg_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
return v_res_128_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(lean_object* v_a_129_, lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
else
{
lean_object* v_key_132_; lean_object* v_tail_133_; lean_object* v_type_134_; lean_object* v_type_135_; uint8_t v___x_136_; 
v_key_132_ = lean_ctor_get(v_x_130_, 0);
v_tail_133_ = lean_ctor_get(v_x_130_, 2);
v_type_134_ = lean_ctor_get(v_key_132_, 1);
v_type_135_ = lean_ctor_get(v_a_129_, 1);
v___x_136_ = lean_expr_eqv(v_type_134_, v_type_135_);
if (v___x_136_ == 0)
{
v_x_130_ = v_tail_133_;
goto _start;
}
else
{
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg___boxed(lean_object* v_a_138_, lean_object* v_x_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_138_, v_x_139_);
lean_dec(v_x_139_);
lean_dec_ref(v_a_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_143_) == 0)
{
return v_x_142_;
}
else
{
lean_object* v_key_144_; lean_object* v_value_145_; lean_object* v_tail_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_170_; 
v_key_144_ = lean_ctor_get(v_x_143_, 0);
v_value_145_ = lean_ctor_get(v_x_143_, 1);
v_tail_146_ = lean_ctor_get(v_x_143_, 2);
v_isSharedCheck_170_ = !lean_is_exclusive(v_x_143_);
if (v_isSharedCheck_170_ == 0)
{
v___x_148_ = v_x_143_;
v_isShared_149_ = v_isSharedCheck_170_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_tail_146_);
lean_inc(v_value_145_);
lean_inc(v_key_144_);
lean_dec(v_x_143_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_170_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v_type_150_; lean_object* v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint64_t v___x_154_; uint64_t v_fold_155_; uint64_t v___x_156_; uint64_t v___x_157_; uint64_t v___x_158_; size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; size_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v_type_150_ = lean_ctor_get(v_key_144_, 1);
v___x_151_ = lean_array_get_size(v_x_142_);
v___x_152_ = l_Lean_Expr_hash(v_type_150_);
v___x_153_ = 32ULL;
v___x_154_ = lean_uint64_shift_right(v___x_152_, v___x_153_);
v_fold_155_ = lean_uint64_xor(v___x_152_, v___x_154_);
v___x_156_ = 16ULL;
v___x_157_ = lean_uint64_shift_right(v_fold_155_, v___x_156_);
v___x_158_ = lean_uint64_xor(v_fold_155_, v___x_157_);
v___x_159_ = lean_uint64_to_usize(v___x_158_);
v___x_160_ = lean_usize_of_nat(v___x_151_);
v___x_161_ = ((size_t)1ULL);
v___x_162_ = lean_usize_sub(v___x_160_, v___x_161_);
v___x_163_ = lean_usize_land(v___x_159_, v___x_162_);
v___x_164_ = lean_array_uget_borrowed(v_x_142_, v___x_163_);
lean_inc(v___x_164_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 2, v___x_164_);
v___x_166_ = v___x_148_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_key_144_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_value_145_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v___x_164_);
v___x_166_ = v_reuseFailAlloc_169_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; 
v___x_167_ = lean_array_uset(v_x_142_, v___x_163_, v___x_166_);
v_x_142_ = v___x_167_;
v_x_143_ = v_tail_146_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(lean_object* v_i_171_, lean_object* v_source_172_, lean_object* v_target_173_){
_start:
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = lean_array_get_size(v_source_172_);
v___x_175_ = lean_nat_dec_lt(v_i_171_, v___x_174_);
if (v___x_175_ == 0)
{
lean_dec_ref(v_source_172_);
lean_dec(v_i_171_);
return v_target_173_;
}
else
{
lean_object* v_es_176_; lean_object* v___x_177_; lean_object* v_source_178_; lean_object* v_target_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_es_176_ = lean_array_fget(v_source_172_, v_i_171_);
v___x_177_ = lean_box(0);
v_source_178_ = lean_array_fset(v_source_172_, v_i_171_, v___x_177_);
v_target_179_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(v_target_173_, v_es_176_);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_i_171_, v___x_180_);
lean_dec(v_i_171_);
v_i_171_ = v___x_181_;
v_source_172_ = v_source_178_;
v_target_173_ = v_target_179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(lean_object* v_data_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_nbuckets_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_184_ = lean_array_get_size(v_data_183_);
v___x_185_ = lean_unsigned_to_nat(2u);
v_nbuckets_186_ = lean_nat_mul(v___x_184_, v___x_185_);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = lean_box(0);
v___x_189_ = lean_mk_array(v_nbuckets_186_, v___x_188_);
v___x_190_ = lean_array_propagate_mark(v_data_183_, v___x_189_);
v___x_191_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v___x_187_, v_data_183_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(lean_object* v_m_192_, lean_object* v_a_193_, lean_object* v_b_194_){
_start:
{
lean_object* v_size_195_; lean_object* v_buckets_196_; lean_object* v_type_197_; lean_object* v___x_198_; uint64_t v___x_199_; uint64_t v___x_200_; uint64_t v___x_201_; uint64_t v_fold_202_; uint64_t v___x_203_; uint64_t v___x_204_; uint64_t v___x_205_; size_t v___x_206_; size_t v___x_207_; size_t v___x_208_; size_t v___x_209_; size_t v___x_210_; lean_object* v_bkt_211_; uint8_t v___x_212_; 
v_size_195_ = lean_ctor_get(v_m_192_, 0);
v_buckets_196_ = lean_ctor_get(v_m_192_, 1);
v_type_197_ = lean_ctor_get(v_a_193_, 1);
v___x_198_ = lean_array_get_size(v_buckets_196_);
v___x_199_ = l_Lean_Expr_hash(v_type_197_);
v___x_200_ = 32ULL;
v___x_201_ = lean_uint64_shift_right(v___x_199_, v___x_200_);
v_fold_202_ = lean_uint64_xor(v___x_199_, v___x_201_);
v___x_203_ = 16ULL;
v___x_204_ = lean_uint64_shift_right(v_fold_202_, v___x_203_);
v___x_205_ = lean_uint64_xor(v_fold_202_, v___x_204_);
v___x_206_ = lean_uint64_to_usize(v___x_205_);
v___x_207_ = lean_usize_of_nat(v___x_198_);
v___x_208_ = ((size_t)1ULL);
v___x_209_ = lean_usize_sub(v___x_207_, v___x_208_);
v___x_210_ = lean_usize_land(v___x_206_, v___x_209_);
v_bkt_211_ = lean_array_uget_borrowed(v_buckets_196_, v___x_210_);
v___x_212_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_193_, v_bkt_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_233_; 
lean_inc_ref(v_buckets_196_);
lean_inc(v_size_195_);
v_isSharedCheck_233_ = !lean_is_exclusive(v_m_192_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; lean_object* v_unused_235_; 
v_unused_234_ = lean_ctor_get(v_m_192_, 1);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v_m_192_, 0);
lean_dec(v_unused_235_);
v___x_214_ = v_m_192_;
v_isShared_215_ = v_isSharedCheck_233_;
goto v_resetjp_213_;
}
else
{
lean_dec(v_m_192_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_233_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v_size_x27_217_; lean_object* v___x_218_; lean_object* v_buckets_x27_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_216_ = lean_unsigned_to_nat(1u);
v_size_x27_217_ = lean_nat_add(v_size_195_, v___x_216_);
lean_dec(v_size_195_);
lean_inc(v_bkt_211_);
v___x_218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_218_, 0, v_a_193_);
lean_ctor_set(v___x_218_, 1, v_b_194_);
lean_ctor_set(v___x_218_, 2, v_bkt_211_);
v_buckets_x27_219_ = lean_array_uset(v_buckets_196_, v___x_210_, v___x_218_);
v___x_220_ = lean_unsigned_to_nat(4u);
v___x_221_ = lean_nat_mul(v_size_x27_217_, v___x_220_);
v___x_222_ = lean_unsigned_to_nat(3u);
v___x_223_ = lean_nat_div(v___x_221_, v___x_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_array_get_size(v_buckets_x27_219_);
v___x_225_ = lean_nat_dec_le(v___x_223_, v___x_224_);
lean_dec(v___x_223_);
if (v___x_225_ == 0)
{
lean_object* v_val_226_; lean_object* v___x_228_; 
v_val_226_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_buckets_x27_219_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v_val_226_);
lean_ctor_set(v___x_214_, 0, v_size_x27_217_);
v___x_228_ = v___x_214_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_size_x27_217_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_val_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
else
{
lean_object* v___x_231_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v_buckets_x27_219_);
lean_ctor_set(v___x_214_, 0, v_size_x27_217_);
v___x_231_ = v___x_214_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_size_x27_217_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_buckets_x27_219_);
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
lean_dec(v_b_194_);
lean_dec_ref(v_a_193_);
return v_m_192_;
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_box(0);
v___x_240_ = lean_unsigned_to_nat(16u);
v___x_241_ = lean_mk_array(v___x_240_, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2);
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_242_);
return v___x_244_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4(void){
_start:
{
lean_object* v___x_245_; lean_object* v_sats_246_; lean_object* v___x_247_; 
v___x_245_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3);
v_sats_246_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1));
v___x_247_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_247_, 0, v_sats_246_);
lean_ctor_set(v___x_247_, 1, v___x_245_);
lean_ctor_set(v___x_247_, 2, v___x_245_);
lean_ctor_set(v___x_247_, 3, v___x_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(lean_object* v_as_248_, size_t v_sz_249_, size_t v_i_250_, lean_object* v_b_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_a_262_; uint8_t v___x_266_; 
v___x_266_ = lean_usize_dec_lt(v_i_250_, v_sz_249_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v_b_251_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0));
v___x_269_ = l_Lean_Core_checkSystem(v___x_268_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec_ref_known(v___x_269_, 1);
v_a_270_ = lean_array_uget_borrowed(v_as_248_, v_i_250_);
lean_inc(v_a_270_);
v___x_271_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed), 11, 1);
lean_closure_set(v___x_271_, 0, v_a_270_);
v___x_272_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4);
v___x_273_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v___x_271_, v___x_272_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v_fst_275_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 1);
v_fst_275_ = lean_ctor_get(v_a_274_, 0);
lean_inc(v_fst_275_);
if (lean_obj_tag(v_fst_275_) == 1)
{
lean_object* v_snd_276_; lean_object* v_fst_277_; lean_object* v_snd_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_288_; 
v_snd_276_ = lean_ctor_get(v_a_274_, 1);
lean_inc(v_snd_276_);
lean_dec(v_a_274_);
v_fst_277_ = lean_ctor_get(v_b_251_, 0);
v_snd_278_ = lean_ctor_get(v_b_251_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v_b_251_);
if (v_isSharedCheck_288_ == 0)
{
v___x_280_ = v_b_251_;
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_snd_278_);
lean_inc(v_fst_277_);
lean_dec(v_b_251_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v_val_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v_val_282_ = lean_ctor_get(v_fst_275_, 0);
lean_inc(v_val_282_);
lean_dec_ref_known(v_fst_275_, 1);
v___x_283_ = l_Array_append___redArg(v_fst_277_, v_snd_276_);
lean_dec(v_snd_276_);
v___x_284_ = lean_array_push(v___x_283_, v_val_282_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_284_);
v___x_286_ = v___x_280_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_snd_278_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
v_a_262_ = v___x_286_;
goto v___jp_261_;
}
}
}
else
{
lean_object* v_fst_289_; lean_object* v_snd_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_299_; 
lean_dec(v_fst_275_);
lean_dec(v_a_274_);
v_fst_289_ = lean_ctor_get(v_b_251_, 0);
v_snd_290_ = lean_ctor_get(v_b_251_, 1);
v_isSharedCheck_299_ = !lean_is_exclusive(v_b_251_);
if (v_isSharedCheck_299_ == 0)
{
v___x_292_ = v_b_251_;
v_isShared_293_ = v_isSharedCheck_299_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_snd_290_);
lean_inc(v_fst_289_);
lean_dec(v_b_251_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_299_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_294_ = lean_box(0);
lean_inc(v_a_270_);
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_snd_290_, v_a_270_, v___x_294_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v___x_295_);
v___x_297_ = v___x_292_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_fst_289_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
v_a_262_ = v___x_297_;
goto v___jp_261_;
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v_b_251_);
v_a_300_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_273_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_273_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v_b_251_);
v_a_308_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_269_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_269_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
v___jp_261_:
{
size_t v___x_263_; size_t v___x_264_; 
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_add(v_i_250_, v___x_263_);
v_i_250_ = v___x_264_;
v_b_251_ = v_a_262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___boxed(lean_object* v_as_316_, lean_object* v_sz_317_, lean_object* v_i_318_, lean_object* v_b_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
size_t v_sz_boxed_329_; size_t v_i_boxed_330_; lean_object* v_res_331_; 
v_sz_boxed_329_ = lean_unbox_usize(v_sz_317_);
lean_dec(v_sz_317_);
v_i_boxed_330_ = lean_unbox_usize(v_i_318_);
lean_dec(v_i_318_);
v_res_331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v_as_316_, v_sz_boxed_329_, v_i_boxed_330_, v_b_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec_ref(v_as_316_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(lean_object* v_a_332_, lean_object* v_b_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_array_341_; lean_object* v_start_342_; lean_object* v_stop_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_358_; 
v_array_341_ = lean_ctor_get(v_a_332_, 0);
v_start_342_ = lean_ctor_get(v_a_332_, 1);
v_stop_343_ = lean_ctor_get(v_a_332_, 2);
v_isSharedCheck_358_ = !lean_is_exclusive(v_a_332_);
if (v_isSharedCheck_358_ == 0)
{
v___x_345_ = v_a_332_;
v_isShared_346_ = v_isSharedCheck_358_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_stop_343_);
lean_inc(v_start_342_);
lean_inc(v_array_341_);
lean_dec(v_a_332_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_358_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
uint8_t v___x_347_; 
v___x_347_ = lean_nat_dec_lt(v_start_342_, v_stop_343_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
lean_del_object(v___x_345_);
lean_dec(v_stop_343_);
lean_dec(v_start_342_);
lean_dec_ref(v_array_341_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v_b_333_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_array_fget_borrowed(v_array_341_, v_start_342_);
lean_inc(v___x_349_);
v___x_350_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_b_333_, v___x_349_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_350_, 1);
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v_start_342_, v___x_352_);
lean_dec(v_start_342_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v___x_353_);
v___x_355_ = v___x_345_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_array_341_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_stop_343_);
v___x_355_ = v_reuseFailAlloc_357_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
v_a_332_ = v___x_355_;
v_b_333_ = v_a_351_;
goto _start;
}
}
else
{
lean_del_object(v___x_345_);
lean_dec(v_stop_343_);
lean_dec(v_start_342_);
lean_dec_ref(v_array_341_);
return v___x_350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg___boxed(lean_object* v_a_359_, lean_object* v_b_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_359_, v_b_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_368_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1));
v___x_373_ = l_Lean_MessageData_ofFormat(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(lean_object* v_sats_374_, lean_object* v_unusedHypotheses_375_, lean_object* v___x_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; size_t v_sz_387_; size_t v___x_388_; lean_object* v___x_389_; 
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_sats_374_);
lean_ctor_set(v___x_386_, 1, v_unusedHypotheses_375_);
v_sz_387_ = lean_array_size(v___y_377_);
v___x_388_ = ((size_t)0ULL);
v___x_389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v___y_377_, v_sz_387_, v___x_388_, v___x_386_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v_fst_391_; lean_object* v_snd_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 1);
v_fst_391_ = lean_ctor_get(v_a_390_, 0);
lean_inc(v_fst_391_);
v_snd_392_ = lean_ctor_get(v_a_390_, 1);
lean_inc(v_snd_392_);
lean_dec(v_a_390_);
v___x_393_ = lean_array_get_size(v_fst_391_);
v___x_394_ = lean_nat_dec_eq(v___x_393_, v___x_376_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_395_ = lean_array_fget(v_fst_391_, v___x_376_);
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = l_Array_toSubarray___redArg(v_fst_391_, v___x_396_, v___x_393_);
v___x_398_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v___x_397_, v___x_395_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_411_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_411_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_411_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_411_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v_bvExpr_403_; lean_object* v_expr_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v_bvExpr_403_ = lean_ctor_get(v_a_399_, 0);
v_expr_404_ = lean_ctor_get(v_a_399_, 2);
lean_inc_ref(v_expr_404_);
lean_inc_ref(v_bvExpr_403_);
v___x_405_ = l_Lean_ShareCommon_shareCommon___redArg(v_bvExpr_403_);
v___x_406_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed), 11, 1);
lean_closure_set(v___x_406_, 0, v_a_399_);
v___x_407_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_ctor_set(v___x_407_, 2, v_snd_392_);
lean_ctor_set(v___x_407_, 3, v_expr_404_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_407_);
v___x_409_ = v___x_401_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_snd_392_);
v_a_412_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_398_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_398_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v_snd_392_);
lean_dec(v_fst_391_);
v___x_420_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2);
v___x_421_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v___x_420_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
return v___x_421_;
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
v_a_422_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_389_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_389_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed(lean_object* v_sats_430_, lean_object* v_unusedHypotheses_431_, lean_object* v___x_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(v_sats_430_, v_unusedHypotheses_431_, v___x_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___x_432_);
return v_res_442_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_box(0);
v___x_444_ = lean_unsigned_to_nat(16u);
v___x_445_ = lean_mk_array(v___x_444_, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v_unusedHypotheses_448_; 
v___x_446_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0);
v___x_447_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_unusedHypotheses_448_, 0, v___x_447_);
lean_ctor_set(v_unusedHypotheses_448_, 1, v___x_446_);
return v_unusedHypotheses_448_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2(void){
_start:
{
lean_object* v___x_449_; lean_object* v_unusedHypotheses_450_; lean_object* v_sats_451_; lean_object* v___f_452_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_450_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1);
v_sats_451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1));
v___f_452_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed), 12, 3);
lean_closure_set(v___f_452_, 0, v_sats_451_);
lean_closure_set(v___f_452_, 1, v_unusedHypotheses_450_);
lean_closure_set(v___f_452_, 2, v___x_449_);
return v___f_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV(lean_object* v_g_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___f_463_; lean_object* v___x_464_; 
v___f_463_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2);
v___x_464_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_g_453_, v___f_463_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___boxed(lean_object* v_g_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0(lean_object* v_00_u03b2_476_, lean_object* v_m_477_, lean_object* v_a_478_, lean_object* v_b_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_m_477_, v_a_478_, v_b_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(lean_object* v_inst_481_, lean_object* v_R_482_, lean_object* v_a_483_, lean_object* v_b_484_, lean_object* v_c_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_483_, v_b_484_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___boxed(lean_object* v_inst_496_, lean_object* v_R_497_, lean_object* v_a_498_, lean_object* v_b_499_, lean_object* v_c_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(v_inst_496_, v_R_497_, v_a_498_, v_b_499_, v_c_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(lean_object* v_00_u03b1_511_, lean_object* v_msg_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_512_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___boxed(lean_object* v_00_u03b1_523_, lean_object* v_msg_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(v_00_u03b1_523_, v_msg_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_534_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(lean_object* v_00_u03b2_535_, lean_object* v_a_536_, lean_object* v_x_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_536_, v_x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___boxed(lean_object* v_00_u03b2_539_, lean_object* v_a_540_, lean_object* v_x_541_){
_start:
{
uint8_t v_res_542_; lean_object* v_r_543_; 
v_res_542_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(v_00_u03b2_539_, v_a_540_, v_x_541_);
lean_dec(v_x_541_);
lean_dec_ref(v_a_540_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1(lean_object* v_00_u03b2_544_, lean_object* v_data_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_data_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_547_, lean_object* v_i_548_, lean_object* v_source_549_, lean_object* v_target_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v_i_548_, v_source_549_, v_target_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_552_, lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(v_x_553_, v_x_554_);
return v___x_555_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_unsigned_to_nat(32u);
v___x_557_ = lean_mk_empty_array_with_capacity(v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1(void){
_start:
{
size_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_559_ = ((size_t)5ULL);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_unsigned_to_nat(32u);
v___x_562_ = lean_mk_empty_array_with_capacity(v___x_561_);
v___x_563_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0);
v___x_564_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_562_);
lean_ctor_set(v___x_564_, 2, v___x_560_);
lean_ctor_set(v___x_564_, 3, v___x_560_);
lean_ctor_set_usize(v___x_564_, 4, v___x_559_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; lean_object* v_traceState_568_; lean_object* v_traces_569_; lean_object* v___x_570_; lean_object* v_traceState_571_; lean_object* v_env_572_; lean_object* v_nextMacroScope_573_; lean_object* v_ngen_574_; lean_object* v_auxDeclNGen_575_; lean_object* v_cache_576_; lean_object* v_messages_577_; lean_object* v_infoState_578_; lean_object* v_snapshotTasks_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_598_; 
v___x_567_ = lean_st_ref_get(v___y_565_);
v_traceState_568_ = lean_ctor_get(v___x_567_, 4);
lean_inc_ref(v_traceState_568_);
lean_dec(v___x_567_);
v_traces_569_ = lean_ctor_get(v_traceState_568_, 0);
lean_inc_ref(v_traces_569_);
lean_dec_ref(v_traceState_568_);
v___x_570_ = lean_st_ref_take(v___y_565_);
v_traceState_571_ = lean_ctor_get(v___x_570_, 4);
v_env_572_ = lean_ctor_get(v___x_570_, 0);
v_nextMacroScope_573_ = lean_ctor_get(v___x_570_, 1);
v_ngen_574_ = lean_ctor_get(v___x_570_, 2);
v_auxDeclNGen_575_ = lean_ctor_get(v___x_570_, 3);
v_cache_576_ = lean_ctor_get(v___x_570_, 5);
v_messages_577_ = lean_ctor_get(v___x_570_, 6);
v_infoState_578_ = lean_ctor_get(v___x_570_, 7);
v_snapshotTasks_579_ = lean_ctor_get(v___x_570_, 8);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_598_ == 0)
{
v___x_581_ = v___x_570_;
v_isShared_582_ = v_isSharedCheck_598_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_snapshotTasks_579_);
lean_inc(v_infoState_578_);
lean_inc(v_messages_577_);
lean_inc(v_cache_576_);
lean_inc(v_traceState_571_);
lean_inc(v_auxDeclNGen_575_);
lean_inc(v_ngen_574_);
lean_inc(v_nextMacroScope_573_);
lean_inc(v_env_572_);
lean_dec(v___x_570_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_598_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
uint64_t v_tid_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_596_; 
v_tid_583_ = lean_ctor_get_uint64(v_traceState_571_, sizeof(void*)*1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_traceState_571_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v_traceState_571_, 0);
lean_dec(v_unused_597_);
v___x_585_ = v_traceState_571_;
v_isShared_586_ = v_isSharedCheck_596_;
goto v_resetjp_584_;
}
else
{
lean_dec(v_traceState_571_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_596_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_587_);
v___x_589_ = v___x_585_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_587_);
lean_ctor_set_uint64(v_reuseFailAlloc_595_, sizeof(void*)*1, v_tid_583_);
v___x_589_ = v_reuseFailAlloc_595_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_591_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 4, v___x_589_);
v___x_591_ = v___x_581_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_env_572_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_nextMacroScope_573_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_ngen_574_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_auxDeclNGen_575_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_594_, 5, v_cache_576_);
lean_ctor_set(v_reuseFailAlloc_594_, 6, v_messages_577_);
lean_ctor_set(v_reuseFailAlloc_594_, 7, v_infoState_578_);
lean_ctor_set(v_reuseFailAlloc_594_, 8, v_snapshotTasks_579_);
v___x_591_ = v_reuseFailAlloc_594_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_st_ref_put(v___y_565_, v___x_591_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v_traces_569_);
return v___x_593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___boxed(lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(v___y_599_);
lean_dec(v___y_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(v___y_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___boxed(lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
return v_res_621_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(lean_object* v_opts_622_, lean_object* v_opt_623_){
_start:
{
lean_object* v_name_624_; lean_object* v_defValue_625_; lean_object* v_map_626_; lean_object* v___x_627_; 
v_name_624_ = lean_ctor_get(v_opt_623_, 0);
v_defValue_625_ = lean_ctor_get(v_opt_623_, 1);
v_map_626_ = lean_ctor_get(v_opts_622_, 0);
v___x_627_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_626_, v_name_624_);
if (lean_obj_tag(v___x_627_) == 0)
{
uint8_t v___x_628_; 
v___x_628_ = lean_unbox(v_defValue_625_);
return v___x_628_;
}
else
{
lean_object* v_val_629_; 
v_val_629_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_val_629_);
lean_dec_ref_known(v___x_627_, 1);
if (lean_obj_tag(v_val_629_) == 1)
{
uint8_t v_v_630_; 
v_v_630_ = lean_ctor_get_uint8(v_val_629_, 0);
lean_dec_ref_known(v_val_629_, 0);
return v_v_630_;
}
else
{
uint8_t v___x_631_; 
lean_dec(v_val_629_);
v___x_631_ = lean_unbox(v_defValue_625_);
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___boxed(lean_object* v_opts_632_, lean_object* v_opt_633_){
_start:
{
uint8_t v_res_634_; lean_object* v_r_635_; 
v_res_634_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_opts_632_, v_opt_633_);
lean_dec_ref(v_opt_633_);
lean_dec_ref(v_opts_632_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1));
v___x_640_ = l_Lean_MessageData_ofFormat(v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(lean_object* v_x_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed(lean_object* v_x_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(v_x_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec_ref(v_x_653_);
return v_res_663_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14(lean_object* v_e_664_){
_start:
{
if (lean_obj_tag(v_e_664_) == 0)
{
uint8_t v___x_665_; 
v___x_665_ = 2;
return v___x_665_;
}
else
{
uint8_t v___x_666_; 
v___x_666_ = 0;
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14___boxed(lean_object* v_e_667_){
_start:
{
uint8_t v_res_668_; lean_object* v_r_669_; 
v_res_668_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14(v_e_667_);
lean_dec_ref(v_e_667_);
v_r_669_ = lean_box(v_res_668_);
return v_r_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(lean_object* v_opts_670_, lean_object* v_opt_671_){
_start:
{
lean_object* v_name_672_; lean_object* v_defValue_673_; lean_object* v_map_674_; lean_object* v___x_675_; 
v_name_672_ = lean_ctor_get(v_opt_671_, 0);
v_defValue_673_ = lean_ctor_get(v_opt_671_, 1);
v_map_674_ = lean_ctor_get(v_opts_670_, 0);
v___x_675_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_674_, v_name_672_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_inc(v_defValue_673_);
return v_defValue_673_;
}
else
{
lean_object* v_val_676_; 
v_val_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_val_676_);
lean_dec_ref_known(v___x_675_, 1);
if (lean_obj_tag(v_val_676_) == 3)
{
lean_object* v_v_677_; 
v_v_677_ = lean_ctor_get(v_val_676_, 0);
lean_inc(v_v_677_);
lean_dec_ref_known(v_val_676_, 1);
return v_v_677_;
}
else
{
lean_dec(v_val_676_);
lean_inc(v_defValue_673_);
return v_defValue_673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15___boxed(lean_object* v_opts_678_, lean_object* v_opt_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(v_opts_678_, v_opt_679_);
lean_dec_ref(v_opt_679_);
lean_dec_ref(v_opts_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17(size_t v_sz_681_, size_t v_i_682_, lean_object* v_bs_683_){
_start:
{
uint8_t v___x_684_; 
v___x_684_ = lean_usize_dec_lt(v_i_682_, v_sz_681_);
if (v___x_684_ == 0)
{
return v_bs_683_;
}
else
{
lean_object* v_v_685_; lean_object* v_msg_686_; lean_object* v___x_687_; lean_object* v_bs_x27_688_; size_t v___x_689_; size_t v___x_690_; lean_object* v___x_691_; 
v_v_685_ = lean_array_uget_borrowed(v_bs_683_, v_i_682_);
v_msg_686_ = lean_ctor_get(v_v_685_, 1);
lean_inc_ref(v_msg_686_);
v___x_687_ = lean_unsigned_to_nat(0u);
v_bs_x27_688_ = lean_array_uset(v_bs_683_, v_i_682_, v___x_687_);
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_add(v_i_682_, v___x_689_);
v___x_691_ = lean_array_uset(v_bs_x27_688_, v_i_682_, v_msg_686_);
v_i_682_ = v___x_690_;
v_bs_683_ = v___x_691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17___boxed(lean_object* v_sz_693_, lean_object* v_i_694_, lean_object* v_bs_695_){
_start:
{
size_t v_sz_boxed_696_; size_t v_i_boxed_697_; lean_object* v_res_698_; 
v_sz_boxed_696_ = lean_unbox_usize(v_sz_693_);
lean_dec(v_sz_693_);
v_i_boxed_697_ = lean_unbox_usize(v_i_694_);
lean_dec(v_i_694_);
v_res_698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17(v_sz_boxed_696_, v_i_boxed_697_, v_bs_695_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg(lean_object* v_oldTraces_699_, lean_object* v_data_700_, lean_object* v_ref_701_, lean_object* v_msg_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_toCold_708_; lean_object* v_currRecDepth_709_; lean_object* v_ref_710_; uint8_t v_diag_711_; uint8_t v_suppressElabErrors_712_; lean_object* v___x_713_; lean_object* v_traceState_714_; lean_object* v_traces_715_; lean_object* v_ref_716_; lean_object* v___x_717_; lean_object* v___x_718_; size_t v_sz_719_; size_t v___x_720_; lean_object* v___x_721_; lean_object* v_msg_722_; lean_object* v___x_723_; lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_761_; 
v_toCold_708_ = lean_ctor_get(v___y_705_, 0);
v_currRecDepth_709_ = lean_ctor_get(v___y_705_, 1);
v_ref_710_ = lean_ctor_get(v___y_705_, 2);
v_diag_711_ = lean_ctor_get_uint8(v___y_705_, sizeof(void*)*3);
v_suppressElabErrors_712_ = lean_ctor_get_uint8(v___y_705_, sizeof(void*)*3 + 1);
v___x_713_ = lean_st_ref_get(v___y_706_);
v_traceState_714_ = lean_ctor_get(v___x_713_, 4);
lean_inc_ref(v_traceState_714_);
lean_dec(v___x_713_);
v_traces_715_ = lean_ctor_get(v_traceState_714_, 0);
lean_inc_ref(v_traces_715_);
lean_dec_ref(v_traceState_714_);
v_ref_716_ = l_Lean_replaceRef(v_ref_701_, v_ref_710_);
lean_inc(v_currRecDepth_709_);
lean_inc_ref(v_toCold_708_);
v___x_717_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_717_, 0, v_toCold_708_);
lean_ctor_set(v___x_717_, 1, v_currRecDepth_709_);
lean_ctor_set(v___x_717_, 2, v_ref_716_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*3, v_diag_711_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*3 + 1, v_suppressElabErrors_712_);
v___x_718_ = l_Lean_PersistentArray_toArray___redArg(v_traces_715_);
lean_dec_ref(v_traces_715_);
v_sz_719_ = lean_array_size(v___x_718_);
v___x_720_ = ((size_t)0ULL);
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17(v_sz_719_, v___x_720_, v___x_718_);
v_msg_722_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_722_, 0, v_data_700_);
lean_ctor_set(v_msg_722_, 1, v_msg_702_);
lean_ctor_set(v_msg_722_, 2, v___x_721_);
v___x_723_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_722_, v___y_703_, v___y_704_, v___x_717_, v___y_706_);
lean_dec_ref_known(v___x_717_, 3);
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_761_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_761_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_761_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v_traceState_729_; lean_object* v_env_730_; lean_object* v_nextMacroScope_731_; lean_object* v_ngen_732_; lean_object* v_auxDeclNGen_733_; lean_object* v_cache_734_; lean_object* v_messages_735_; lean_object* v_infoState_736_; lean_object* v_snapshotTasks_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_760_; 
v___x_728_ = lean_st_ref_take(v___y_706_);
v_traceState_729_ = lean_ctor_get(v___x_728_, 4);
v_env_730_ = lean_ctor_get(v___x_728_, 0);
v_nextMacroScope_731_ = lean_ctor_get(v___x_728_, 1);
v_ngen_732_ = lean_ctor_get(v___x_728_, 2);
v_auxDeclNGen_733_ = lean_ctor_get(v___x_728_, 3);
v_cache_734_ = lean_ctor_get(v___x_728_, 5);
v_messages_735_ = lean_ctor_get(v___x_728_, 6);
v_infoState_736_ = lean_ctor_get(v___x_728_, 7);
v_snapshotTasks_737_ = lean_ctor_get(v___x_728_, 8);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_760_ == 0)
{
v___x_739_ = v___x_728_;
v_isShared_740_ = v_isSharedCheck_760_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snapshotTasks_737_);
lean_inc(v_infoState_736_);
lean_inc(v_messages_735_);
lean_inc(v_cache_734_);
lean_inc(v_traceState_729_);
lean_inc(v_auxDeclNGen_733_);
lean_inc(v_ngen_732_);
lean_inc(v_nextMacroScope_731_);
lean_inc(v_env_730_);
lean_dec(v___x_728_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_760_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
uint64_t v_tid_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_758_; 
v_tid_741_ = lean_ctor_get_uint64(v_traceState_729_, sizeof(void*)*1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_traceState_729_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v_traceState_729_, 0);
lean_dec(v_unused_759_);
v___x_743_ = v_traceState_729_;
v_isShared_744_ = v_isSharedCheck_758_;
goto v_resetjp_742_;
}
else
{
lean_dec(v_traceState_729_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_758_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v_ref_701_);
lean_ctor_set(v___x_745_, 1, v_a_724_);
v___x_746_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_699_, v___x_745_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_746_);
v___x_748_ = v___x_743_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_746_);
lean_ctor_set_uint64(v_reuseFailAlloc_757_, sizeof(void*)*1, v_tid_741_);
v___x_748_ = v_reuseFailAlloc_757_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_750_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 4, v___x_748_);
v___x_750_ = v___x_739_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_env_730_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_nextMacroScope_731_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_ngen_732_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v_auxDeclNGen_733_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_756_, 5, v_cache_734_);
lean_ctor_set(v_reuseFailAlloc_756_, 6, v_messages_735_);
lean_ctor_set(v_reuseFailAlloc_756_, 7, v_infoState_736_);
lean_ctor_set(v_reuseFailAlloc_756_, 8, v_snapshotTasks_737_);
v___x_750_ = v_reuseFailAlloc_756_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_751_ = lean_st_ref_put(v___y_706_, v___x_750_);
v___x_752_ = lean_box(0);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_752_);
v___x_754_ = v___x_726_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg___boxed(lean_object* v_oldTraces_762_, lean_object* v_data_763_, lean_object* v_ref_764_, lean_object* v_msg_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg(v_oldTraces_762_, v_data_763_, v_ref_764_, v_msg_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(lean_object* v_x_772_){
_start:
{
if (lean_obj_tag(v_x_772_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
v_a_774_ = lean_ctor_get(v_x_772_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v_x_772_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v_x_772_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v_x_772_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set_tag(v___x_776_, 1);
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
v_a_782_ = lean_ctor_get(v_x_772_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v_x_772_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v_x_772_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v_x_772_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set_tag(v___x_784_, 0);
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg___boxed(lean_object* v_x_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_x_790_);
return v_res_792_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0(void){
_start:
{
lean_object* v___x_793_; double v___x_794_; 
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_float_of_nat(v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__1));
v___x_797_ = l_Lean_stringToMessageData(v___x_796_);
return v___x_797_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3(void){
_start:
{
lean_object* v___x_798_; double v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(1000u);
v___x_799_ = lean_float_of_nat(v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(lean_object* v_cls_800_, uint8_t v_collapsed_801_, lean_object* v_tag_802_, lean_object* v_opts_803_, uint8_t v_clsEnabled_804_, lean_object* v_oldTraces_805_, lean_object* v_msg_806_, lean_object* v_resStartStop_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_fst_817_; lean_object* v_snd_818_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v_data_822_; lean_object* v_fst_833_; lean_object* v_snd_834_; lean_object* v___x_835_; uint8_t v___x_836_; lean_object* v___y_838_; lean_object* v_a_839_; uint8_t v___y_854_; double v___y_885_; 
v_fst_817_ = lean_ctor_get(v_resStartStop_807_, 0);
lean_inc(v_fst_817_);
v_snd_818_ = lean_ctor_get(v_resStartStop_807_, 1);
lean_inc(v_snd_818_);
lean_dec_ref(v_resStartStop_807_);
v_fst_833_ = lean_ctor_get(v_snd_818_, 0);
lean_inc(v_fst_833_);
v_snd_834_ = lean_ctor_get(v_snd_818_, 1);
lean_inc(v_snd_834_);
lean_dec(v_snd_818_);
v___x_835_ = l_Lean_trace_profiler;
v___x_836_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_opts_803_, v___x_835_);
if (v___x_836_ == 0)
{
v___y_854_ = v___x_836_;
goto v___jp_853_;
}
else
{
lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_890_ = l_Lean_trace_profiler_useHeartbeats;
v___x_891_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_opts_803_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; double v___x_894_; double v___x_895_; double v___x_896_; 
v___x_892_ = l_Lean_trace_profiler_threshold;
v___x_893_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(v_opts_803_, v___x_892_);
v___x_894_ = lean_float_of_nat(v___x_893_);
v___x_895_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3);
v___x_896_ = lean_float_div(v___x_894_, v___x_895_);
v___y_885_ = v___x_896_;
goto v___jp_884_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; double v___x_899_; 
v___x_897_ = l_Lean_trace_profiler_threshold;
v___x_898_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(v_opts_803_, v___x_897_);
v___x_899_ = lean_float_of_nat(v___x_898_);
v___y_885_ = v___x_899_;
goto v___jp_884_;
}
}
v___jp_819_:
{
lean_object* v___x_823_; 
lean_inc(v___y_821_);
v___x_823_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg(v_oldTraces_805_, v_data_822_, v___y_821_, v___y_820_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v___x_824_; 
lean_dec_ref_known(v___x_823_, 1);
v___x_824_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_fst_817_);
return v___x_824_;
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_fst_817_);
v_a_825_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_823_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_823_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
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
v___jp_837_:
{
uint8_t v_result_840_; lean_object* v___x_841_; lean_object* v___x_842_; double v___x_843_; lean_object* v_data_844_; 
v_result_840_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14(v_fst_817_);
v___x_841_ = lean_box(v_result_840_);
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
v___x_843_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0);
lean_inc_ref(v_tag_802_);
lean_inc_ref(v___x_842_);
lean_inc(v_cls_800_);
v_data_844_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_844_, 0, v_cls_800_);
lean_ctor_set(v_data_844_, 1, v___x_842_);
lean_ctor_set(v_data_844_, 2, v_tag_802_);
lean_ctor_set_float(v_data_844_, sizeof(void*)*3, v___x_843_);
lean_ctor_set_float(v_data_844_, sizeof(void*)*3 + 8, v___x_843_);
lean_ctor_set_uint8(v_data_844_, sizeof(void*)*3 + 16, v_collapsed_801_);
if (v___x_836_ == 0)
{
lean_dec_ref_known(v___x_842_, 1);
lean_dec(v_snd_834_);
lean_dec(v_fst_833_);
lean_dec_ref(v_tag_802_);
lean_dec(v_cls_800_);
v___y_820_ = v_a_839_;
v___y_821_ = v___y_838_;
v_data_822_ = v_data_844_;
goto v___jp_819_;
}
else
{
lean_object* v_data_845_; double v___x_846_; double v___x_847_; 
lean_dec_ref_known(v_data_844_, 3);
v_data_845_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_845_, 0, v_cls_800_);
lean_ctor_set(v_data_845_, 1, v___x_842_);
lean_ctor_set(v_data_845_, 2, v_tag_802_);
v___x_846_ = lean_unbox_float(v_fst_833_);
lean_dec(v_fst_833_);
lean_ctor_set_float(v_data_845_, sizeof(void*)*3, v___x_846_);
v___x_847_ = lean_unbox_float(v_snd_834_);
lean_dec(v_snd_834_);
lean_ctor_set_float(v_data_845_, sizeof(void*)*3 + 8, v___x_847_);
lean_ctor_set_uint8(v_data_845_, sizeof(void*)*3 + 16, v_collapsed_801_);
v___y_820_ = v_a_839_;
v___y_821_ = v___y_838_;
v_data_822_ = v_data_845_;
goto v___jp_819_;
}
}
v___jp_848_:
{
lean_object* v_ref_849_; lean_object* v___x_850_; 
v_ref_849_ = lean_ctor_get(v___y_814_, 2);
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
lean_inc(v___y_809_);
lean_inc_ref(v___y_808_);
lean_inc(v_fst_817_);
v___x_850_ = lean_apply_10(v_msg_806_, v_fst_817_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, lean_box(0));
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v___y_838_ = v_ref_849_;
v_a_839_ = v_a_851_;
goto v___jp_837_;
}
else
{
lean_object* v___x_852_; 
lean_dec_ref_known(v___x_850_, 1);
v___x_852_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2);
v___y_838_ = v_ref_849_;
v_a_839_ = v___x_852_;
goto v___jp_837_;
}
}
v___jp_853_:
{
if (v_clsEnabled_804_ == 0)
{
if (v___y_854_ == 0)
{
lean_object* v___x_855_; lean_object* v_traceState_856_; lean_object* v_env_857_; lean_object* v_nextMacroScope_858_; lean_object* v_ngen_859_; lean_object* v_auxDeclNGen_860_; lean_object* v_cache_861_; lean_object* v_messages_862_; lean_object* v_infoState_863_; lean_object* v_snapshotTasks_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_snd_834_);
lean_dec(v_fst_833_);
lean_dec_ref(v_msg_806_);
lean_dec_ref(v_tag_802_);
lean_dec(v_cls_800_);
v___x_855_ = lean_st_ref_take(v___y_815_);
v_traceState_856_ = lean_ctor_get(v___x_855_, 4);
v_env_857_ = lean_ctor_get(v___x_855_, 0);
v_nextMacroScope_858_ = lean_ctor_get(v___x_855_, 1);
v_ngen_859_ = lean_ctor_get(v___x_855_, 2);
v_auxDeclNGen_860_ = lean_ctor_get(v___x_855_, 3);
v_cache_861_ = lean_ctor_get(v___x_855_, 5);
v_messages_862_ = lean_ctor_get(v___x_855_, 6);
v_infoState_863_ = lean_ctor_get(v___x_855_, 7);
v_snapshotTasks_864_ = lean_ctor_get(v___x_855_, 8);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_883_ == 0)
{
v___x_866_ = v___x_855_;
v_isShared_867_ = v_isSharedCheck_883_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_snapshotTasks_864_);
lean_inc(v_infoState_863_);
lean_inc(v_messages_862_);
lean_inc(v_cache_861_);
lean_inc(v_traceState_856_);
lean_inc(v_auxDeclNGen_860_);
lean_inc(v_ngen_859_);
lean_inc(v_nextMacroScope_858_);
lean_inc(v_env_857_);
lean_dec(v___x_855_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_883_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint64_t v_tid_868_; lean_object* v_traces_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_882_; 
v_tid_868_ = lean_ctor_get_uint64(v_traceState_856_, sizeof(void*)*1);
v_traces_869_ = lean_ctor_get(v_traceState_856_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v_traceState_856_);
if (v_isSharedCheck_882_ == 0)
{
v___x_871_ = v_traceState_856_;
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_traces_869_);
lean_dec(v_traceState_856_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_805_, v_traces_869_);
lean_dec_ref(v_traces_869_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_873_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_873_);
lean_ctor_set_uint64(v_reuseFailAlloc_881_, sizeof(void*)*1, v_tid_868_);
v___x_875_ = v_reuseFailAlloc_881_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v___x_875_);
v___x_877_ = v___x_866_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_env_857_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_nextMacroScope_858_);
lean_ctor_set(v_reuseFailAlloc_880_, 2, v_ngen_859_);
lean_ctor_set(v_reuseFailAlloc_880_, 3, v_auxDeclNGen_860_);
lean_ctor_set(v_reuseFailAlloc_880_, 4, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_880_, 5, v_cache_861_);
lean_ctor_set(v_reuseFailAlloc_880_, 6, v_messages_862_);
lean_ctor_set(v_reuseFailAlloc_880_, 7, v_infoState_863_);
lean_ctor_set(v_reuseFailAlloc_880_, 8, v_snapshotTasks_864_);
v___x_877_ = v_reuseFailAlloc_880_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_st_ref_put(v___y_815_, v___x_877_);
v___x_879_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_fst_817_);
return v___x_879_;
}
}
}
}
}
else
{
goto v___jp_848_;
}
}
else
{
goto v___jp_848_;
}
}
v___jp_884_:
{
double v___x_886_; double v___x_887_; double v___x_888_; uint8_t v___x_889_; 
v___x_886_ = lean_unbox_float(v_snd_834_);
v___x_887_ = lean_unbox_float(v_fst_833_);
v___x_888_ = lean_float_sub(v___x_886_, v___x_887_);
v___x_889_ = lean_float_decLt(v___y_885_, v___x_888_);
v___y_854_ = v___x_889_;
goto v___jp_853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___boxed(lean_object** _args){
lean_object* v_cls_900_ = _args[0];
lean_object* v_collapsed_901_ = _args[1];
lean_object* v_tag_902_ = _args[2];
lean_object* v_opts_903_ = _args[3];
lean_object* v_clsEnabled_904_ = _args[4];
lean_object* v_oldTraces_905_ = _args[5];
lean_object* v_msg_906_ = _args[6];
lean_object* v_resStartStop_907_ = _args[7];
lean_object* v___y_908_ = _args[8];
lean_object* v___y_909_ = _args[9];
lean_object* v___y_910_ = _args[10];
lean_object* v___y_911_ = _args[11];
lean_object* v___y_912_ = _args[12];
lean_object* v___y_913_ = _args[13];
lean_object* v___y_914_ = _args[14];
lean_object* v___y_915_ = _args[15];
lean_object* v___y_916_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_917_; uint8_t v_clsEnabled_boxed_918_; lean_object* v_res_919_; 
v_collapsed_boxed_917_ = lean_unbox(v_collapsed_901_);
v_clsEnabled_boxed_918_ = lean_unbox(v_clsEnabled_904_);
v_res_919_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(v_cls_900_, v_collapsed_boxed_917_, v_tag_902_, v_opts_903_, v_clsEnabled_boxed_918_, v_oldTraces_905_, v_msg_906_, v_resStartStop_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec_ref(v_opts_903_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_921_) == 0)
{
lean_inc(v_x_920_);
return v_x_920_;
}
else
{
lean_object* v_key_922_; lean_object* v_value_923_; lean_object* v_tail_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_key_922_ = lean_ctor_get(v_x_921_, 0);
v_value_923_ = lean_ctor_get(v_x_921_, 1);
v_tail_924_ = lean_ctor_get(v_x_921_, 2);
v___x_925_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_x_920_, v_tail_924_);
lean_inc(v_value_923_);
lean_inc(v_key_922_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_key_922_);
lean_ctor_set(v___x_926_, 1, v_value_923_);
v___x_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_925_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___boxed(lean_object* v_x_928_, lean_object* v_x_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_x_928_, v_x_929_);
lean_dec(v_x_929_);
lean_dec(v_x_928_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(lean_object* v_as_931_, size_t v_i_932_, size_t v_stop_933_, lean_object* v_b_934_){
_start:
{
uint8_t v___x_935_; 
v___x_935_ = lean_usize_dec_eq(v_i_932_, v_stop_933_);
if (v___x_935_ == 0)
{
size_t v___x_936_; size_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_936_ = ((size_t)1ULL);
v___x_937_ = lean_usize_sub(v_i_932_, v___x_936_);
v___x_938_ = lean_array_uget_borrowed(v_as_931_, v___x_937_);
v___x_939_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_b_934_, v___x_938_);
lean_dec(v_b_934_);
v_i_932_ = v___x_937_;
v_b_934_ = v___x_939_;
goto _start;
}
else
{
return v_b_934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___boxed(lean_object* v_as_941_, lean_object* v_i_942_, lean_object* v_stop_943_, lean_object* v_b_944_){
_start:
{
size_t v_i_boxed_945_; size_t v_stop_boxed_946_; lean_object* v_res_947_; 
v_i_boxed_945_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_stop_boxed_946_ = lean_unbox_usize(v_stop_943_);
lean_dec(v_stop_943_);
v_res_947_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_as_941_, v_i_boxed_945_, v_stop_boxed_946_, v_b_944_);
lean_dec_ref(v_as_941_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(lean_object* v_x_955_){
_start:
{
switch(lean_obj_tag(v_x_955_))
{
case 0:
{
lean_object* v_a_956_; lean_object* v___x_957_; 
v_a_956_ = lean_ctor_get(v_x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v_x_955_, 1);
v___x_957_ = l_Std_Tactic_BVDecide_BVPred_toString(v_a_956_);
return v___x_957_;
}
case 1:
{
uint8_t v_a_958_; 
v_a_958_ = lean_ctor_get_uint8(v_x_955_, 0);
lean_dec_ref_known(v_x_955_, 0);
if (v_a_958_ == 0)
{
lean_object* v___x_959_; 
v___x_959_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__0));
return v___x_959_;
}
else
{
lean_object* v___x_960_; 
v___x_960_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__1));
return v___x_960_;
}
}
case 2:
{
lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_a_961_ = lean_ctor_get(v_x_955_, 0);
lean_inc_ref(v_a_961_);
lean_dec_ref_known(v_x_955_, 1);
v___x_962_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__2));
v___x_963_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_961_);
v___x_964_ = lean_string_append(v___x_962_, v___x_963_);
lean_dec_ref(v___x_963_);
return v___x_964_;
}
case 3:
{
uint8_t v_a_965_; lean_object* v_a_966_; lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_a_965_ = lean_ctor_get_uint8(v_x_955_, sizeof(void*)*2);
v_a_966_ = lean_ctor_get(v_x_955_, 0);
lean_inc_ref(v_a_966_);
v_a_967_ = lean_ctor_get(v_x_955_, 1);
lean_inc_ref(v_a_967_);
lean_dec_ref_known(v_x_955_, 2);
v___x_968_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__3));
v___x_969_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_966_);
v___x_970_ = lean_string_append(v___x_968_, v___x_969_);
lean_dec_ref(v___x_969_);
v___x_971_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4));
v___x_972_ = lean_string_append(v___x_970_, v___x_971_);
v___x_973_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_965_);
v___x_974_ = lean_string_append(v___x_972_, v___x_973_);
lean_dec_ref(v___x_973_);
v___x_975_ = lean_string_append(v___x_974_, v___x_971_);
v___x_976_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_967_);
v___x_977_ = lean_string_append(v___x_975_, v___x_976_);
lean_dec_ref(v___x_976_);
v___x_978_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__5));
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
return v___x_979_;
}
default: 
{
lean_object* v_a_980_; lean_object* v_a_981_; lean_object* v_a_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_a_980_ = lean_ctor_get(v_x_955_, 0);
lean_inc_ref(v_a_980_);
v_a_981_ = lean_ctor_get(v_x_955_, 1);
lean_inc_ref(v_a_981_);
v_a_982_ = lean_ctor_get(v_x_955_, 2);
lean_inc_ref(v_a_982_);
lean_dec_ref_known(v_x_955_, 3);
v___x_983_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__6));
v___x_984_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_980_);
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
lean_dec_ref(v___x_984_);
v___x_986_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4));
v___x_987_ = lean_string_append(v___x_985_, v___x_986_);
v___x_988_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_981_);
v___x_989_ = lean_string_append(v___x_987_, v___x_988_);
lean_dec_ref(v___x_988_);
v___x_990_ = lean_string_append(v___x_989_, v___x_986_);
v___x_991_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_982_);
v___x_992_ = lean_string_append(v___x_990_, v___x_991_);
lean_dec_ref(v___x_991_);
v___x_993_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__5));
v___x_994_ = lean_string_append(v___x_992_, v___x_993_);
return v___x_994_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(lean_object* v_a_995_, lean_object* v_x_996_){
_start:
{
if (lean_obj_tag(v_x_996_) == 0)
{
uint8_t v___x_997_; 
v___x_997_ = 0;
return v___x_997_;
}
else
{
lean_object* v_key_998_; lean_object* v_tail_999_; uint8_t v___x_1000_; 
v_key_998_ = lean_ctor_get(v_x_996_, 0);
v_tail_999_ = lean_ctor_get(v_x_996_, 2);
v___x_1000_ = lean_nat_dec_eq(v_key_998_, v_a_995_);
if (v___x_1000_ == 0)
{
v_x_996_ = v_tail_999_;
goto _start;
}
else
{
return v___x_1000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_a_1002_, lean_object* v_x_1003_){
_start:
{
uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_res_1004_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(v_a_1002_, v_x_1003_);
lean_dec(v_x_1003_);
lean_dec(v_a_1002_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(lean_object* v_a_1006_, lean_object* v_b_1007_, lean_object* v_x_1008_){
_start:
{
if (lean_obj_tag(v_x_1008_) == 0)
{
lean_dec(v_b_1007_);
lean_dec(v_a_1006_);
return v_x_1008_;
}
else
{
lean_object* v_key_1009_; lean_object* v_value_1010_; lean_object* v_tail_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1023_; 
v_key_1009_ = lean_ctor_get(v_x_1008_, 0);
v_value_1010_ = lean_ctor_get(v_x_1008_, 1);
v_tail_1011_ = lean_ctor_get(v_x_1008_, 2);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_x_1008_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1013_ = v_x_1008_;
v_isShared_1014_ = v_isSharedCheck_1023_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_tail_1011_);
lean_inc(v_value_1010_);
lean_inc(v_key_1009_);
lean_dec(v_x_1008_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1023_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
uint8_t v___x_1015_; 
v___x_1015_ = lean_nat_dec_eq(v_key_1009_, v_a_1006_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(v_a_1006_, v_b_1007_, v_tail_1011_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 2, v___x_1016_);
v___x_1018_ = v___x_1013_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_key_1009_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_value_1010_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
else
{
lean_object* v___x_1021_; 
lean_dec(v_value_1010_);
lean_dec(v_key_1009_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v_b_1007_);
lean_ctor_set(v___x_1013_, 0, v_a_1006_);
v___x_1021_ = v___x_1013_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1006_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_b_1007_);
lean_ctor_set(v_reuseFailAlloc_1022_, 2, v_tail_1011_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19___redArg(lean_object* v_x_1024_, lean_object* v_x_1025_){
_start:
{
if (lean_obj_tag(v_x_1025_) == 0)
{
return v_x_1024_;
}
else
{
lean_object* v_key_1026_; lean_object* v_value_1027_; lean_object* v_tail_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1051_; 
v_key_1026_ = lean_ctor_get(v_x_1025_, 0);
v_value_1027_ = lean_ctor_get(v_x_1025_, 1);
v_tail_1028_ = lean_ctor_get(v_x_1025_, 2);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_x_1025_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1030_ = v_x_1025_;
v_isShared_1031_ = v_isSharedCheck_1051_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_tail_1028_);
lean_inc(v_value_1027_);
lean_inc(v_key_1026_);
lean_dec(v_x_1025_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1051_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; uint64_t v___x_1033_; uint64_t v___x_1034_; uint64_t v___x_1035_; uint64_t v_fold_1036_; uint64_t v___x_1037_; uint64_t v___x_1038_; uint64_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; size_t v___x_1043_; size_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1032_ = lean_array_get_size(v_x_1024_);
v___x_1033_ = lean_uint64_of_nat(v_key_1026_);
v___x_1034_ = 32ULL;
v___x_1035_ = lean_uint64_shift_right(v___x_1033_, v___x_1034_);
v_fold_1036_ = lean_uint64_xor(v___x_1033_, v___x_1035_);
v___x_1037_ = 16ULL;
v___x_1038_ = lean_uint64_shift_right(v_fold_1036_, v___x_1037_);
v___x_1039_ = lean_uint64_xor(v_fold_1036_, v___x_1038_);
v___x_1040_ = lean_uint64_to_usize(v___x_1039_);
v___x_1041_ = lean_usize_of_nat(v___x_1032_);
v___x_1042_ = ((size_t)1ULL);
v___x_1043_ = lean_usize_sub(v___x_1041_, v___x_1042_);
v___x_1044_ = lean_usize_land(v___x_1040_, v___x_1043_);
v___x_1045_ = lean_array_uget_borrowed(v_x_1024_, v___x_1044_);
lean_inc(v___x_1045_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 2, v___x_1045_);
v___x_1047_ = v___x_1030_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_key_1026_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_value_1027_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_array_uset(v_x_1024_, v___x_1044_, v___x_1047_);
v_x_1024_ = v___x_1048_;
v_x_1025_ = v_tail_1028_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15___redArg(lean_object* v_i_1052_, lean_object* v_source_1053_, lean_object* v_target_1054_){
_start:
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = lean_array_get_size(v_source_1053_);
v___x_1056_ = lean_nat_dec_lt(v_i_1052_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_dec_ref(v_source_1053_);
lean_dec(v_i_1052_);
return v_target_1054_;
}
else
{
lean_object* v_es_1057_; lean_object* v___x_1058_; lean_object* v_source_1059_; lean_object* v_target_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_es_1057_ = lean_array_fget(v_source_1053_, v_i_1052_);
v___x_1058_ = lean_box(0);
v_source_1059_ = lean_array_fset(v_source_1053_, v_i_1052_, v___x_1058_);
v_target_1060_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19___redArg(v_target_1054_, v_es_1057_);
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_nat_add(v_i_1052_, v___x_1061_);
lean_dec(v_i_1052_);
v_i_1052_ = v___x_1062_;
v_source_1053_ = v_source_1059_;
v_target_1054_ = v_target_1060_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5___redArg(lean_object* v_data_1064_){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v_nbuckets_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1065_ = lean_array_get_size(v_data_1064_);
v___x_1066_ = lean_unsigned_to_nat(2u);
v_nbuckets_1067_ = lean_nat_mul(v___x_1065_, v___x_1066_);
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_mk_array(v_nbuckets_1067_, v___x_1069_);
v___x_1071_ = lean_array_propagate_mark(v_data_1064_, v___x_1070_);
v___x_1072_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15___redArg(v___x_1068_, v_data_1064_, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1___redArg(lean_object* v_m_1073_, lean_object* v_a_1074_, lean_object* v_b_1075_){
_start:
{
lean_object* v_size_1076_; lean_object* v_buckets_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1120_; 
v_size_1076_ = lean_ctor_get(v_m_1073_, 0);
v_buckets_1077_ = lean_ctor_get(v_m_1073_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_m_1073_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1079_ = v_m_1073_;
v_isShared_1080_ = v_isSharedCheck_1120_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_buckets_1077_);
lean_inc(v_size_1076_);
lean_dec(v_m_1073_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1120_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; uint64_t v___x_1082_; uint64_t v___x_1083_; uint64_t v___x_1084_; uint64_t v_fold_1085_; uint64_t v___x_1086_; uint64_t v___x_1087_; uint64_t v___x_1088_; size_t v___x_1089_; size_t v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; size_t v___x_1093_; lean_object* v_bkt_1094_; uint8_t v___x_1095_; 
v___x_1081_ = lean_array_get_size(v_buckets_1077_);
v___x_1082_ = lean_uint64_of_nat(v_a_1074_);
v___x_1083_ = 32ULL;
v___x_1084_ = lean_uint64_shift_right(v___x_1082_, v___x_1083_);
v_fold_1085_ = lean_uint64_xor(v___x_1082_, v___x_1084_);
v___x_1086_ = 16ULL;
v___x_1087_ = lean_uint64_shift_right(v_fold_1085_, v___x_1086_);
v___x_1088_ = lean_uint64_xor(v_fold_1085_, v___x_1087_);
v___x_1089_ = lean_uint64_to_usize(v___x_1088_);
v___x_1090_ = lean_usize_of_nat(v___x_1081_);
v___x_1091_ = ((size_t)1ULL);
v___x_1092_ = lean_usize_sub(v___x_1090_, v___x_1091_);
v___x_1093_ = lean_usize_land(v___x_1089_, v___x_1092_);
v_bkt_1094_ = lean_array_uget_borrowed(v_buckets_1077_, v___x_1093_);
v___x_1095_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(v_a_1074_, v_bkt_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v_size_x27_1097_; lean_object* v___x_1098_; lean_object* v_buckets_x27_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1096_ = lean_unsigned_to_nat(1u);
v_size_x27_1097_ = lean_nat_add(v_size_1076_, v___x_1096_);
lean_dec(v_size_1076_);
lean_inc(v_bkt_1094_);
v___x_1098_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1098_, 0, v_a_1074_);
lean_ctor_set(v___x_1098_, 1, v_b_1075_);
lean_ctor_set(v___x_1098_, 2, v_bkt_1094_);
v_buckets_x27_1099_ = lean_array_uset(v_buckets_1077_, v___x_1093_, v___x_1098_);
v___x_1100_ = lean_unsigned_to_nat(4u);
v___x_1101_ = lean_nat_mul(v_size_x27_1097_, v___x_1100_);
v___x_1102_ = lean_unsigned_to_nat(3u);
v___x_1103_ = lean_nat_div(v___x_1101_, v___x_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_array_get_size(v_buckets_x27_1099_);
v___x_1105_ = lean_nat_dec_le(v___x_1103_, v___x_1104_);
lean_dec(v___x_1103_);
if (v___x_1105_ == 0)
{
lean_object* v_val_1106_; lean_object* v___x_1108_; 
v_val_1106_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5___redArg(v_buckets_x27_1099_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v_val_1106_);
lean_ctor_set(v___x_1079_, 0, v_size_x27_1097_);
v___x_1108_ = v___x_1079_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_size_x27_1097_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_val_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
else
{
lean_object* v___x_1111_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v_buckets_x27_1099_);
lean_ctor_set(v___x_1079_, 0, v_size_x27_1097_);
v___x_1111_ = v___x_1079_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_size_x27_1097_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_buckets_x27_1099_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
else
{
lean_object* v___x_1113_; lean_object* v_buckets_x27_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
lean_inc(v_bkt_1094_);
v___x_1113_ = lean_box(0);
v_buckets_x27_1114_ = lean_array_uset(v_buckets_1077_, v___x_1093_, v___x_1113_);
v___x_1115_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(v_a_1074_, v_b_1075_, v_bkt_1094_);
v___x_1116_ = lean_array_uset(v_buckets_x27_1114_, v___x_1093_, v___x_1115_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v___x_1116_);
v___x_1118_ = v___x_1079_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_size_1076_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(lean_object* v_as_x27_1121_, lean_object* v_b_1122_){
_start:
{
if (lean_obj_tag(v_as_x27_1121_) == 0)
{
return v_b_1122_;
}
else
{
lean_object* v_head_1123_; lean_object* v_tail_1124_; lean_object* v_fst_1125_; lean_object* v_snd_1126_; lean_object* v_r_1127_; 
v_head_1123_ = lean_ctor_get(v_as_x27_1121_, 0);
v_tail_1124_ = lean_ctor_get(v_as_x27_1121_, 1);
v_fst_1125_ = lean_ctor_get(v_head_1123_, 0);
v_snd_1126_ = lean_ctor_get(v_head_1123_, 1);
lean_inc(v_snd_1126_);
lean_inc(v_fst_1125_);
v_r_1127_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1___redArg(v_b_1122_, v_fst_1125_, v_snd_1126_);
v_as_x27_1121_ = v_tail_1124_;
v_b_1122_ = v_r_1127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg___boxed(lean_object* v_as_x27_1129_, lean_object* v_b_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v_as_x27_1129_, v_b_1130_);
lean_dec(v_as_x27_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(lean_object* v_m_1132_, lean_object* v_l_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v_l_1133_, v_m_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___boxed(lean_object* v_m_1135_, lean_object* v_l_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(v_m_1135_, v_l_1136_);
lean_dec(v_l_1136_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23___redArg(lean_object* v_x_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v_ks_1142_; lean_object* v_vs_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1167_; 
v_ks_1142_ = lean_ctor_get(v_x_1138_, 0);
v_vs_1143_ = lean_ctor_get(v_x_1138_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_x_1138_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1145_ = v_x_1138_;
v_isShared_1146_ = v_isSharedCheck_1167_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_vs_1143_);
lean_inc(v_ks_1142_);
lean_dec(v_x_1138_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1167_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = lean_array_get_size(v_ks_1142_);
v___x_1148_ = lean_nat_dec_lt(v_x_1139_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
lean_dec(v_x_1139_);
v___x_1149_ = lean_array_push(v_ks_1142_, v_x_1140_);
v___x_1150_ = lean_array_push(v_vs_1143_, v_x_1141_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1150_);
lean_ctor_set(v___x_1145_, 0, v___x_1149_);
v___x_1152_ = v___x_1145_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
lean_object* v_k_x27_1154_; uint8_t v___x_1155_; 
v_k_x27_1154_ = lean_array_fget_borrowed(v_ks_1142_, v_x_1139_);
v___x_1155_ = l_Lean_instBEqMVarId_beq(v_x_1140_, v_k_x27_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1157_; 
if (v_isShared_1146_ == 0)
{
v___x_1157_ = v___x_1145_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_ks_1142_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_vs_1143_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_add(v_x_1139_, v___x_1158_);
lean_dec(v_x_1139_);
v_x_1138_ = v___x_1157_;
v_x_1139_ = v___x_1159_;
goto _start;
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1162_ = lean_array_fset(v_ks_1142_, v_x_1139_, v_x_1140_);
v___x_1163_ = lean_array_fset(v_vs_1143_, v_x_1139_, v_x_1141_);
lean_dec(v_x_1139_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1163_);
lean_ctor_set(v___x_1145_, 0, v___x_1162_);
v___x_1165_ = v___x_1145_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1163_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20___redArg(lean_object* v_n_1168_, lean_object* v_k_1169_, lean_object* v_v_1170_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23___redArg(v_n_1168_, v___x_1171_, v_k_1169_, v_v_1170_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(lean_object* v_x_1174_, size_t v_x_1175_, size_t v_x_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
if (lean_obj_tag(v_x_1174_) == 0)
{
lean_object* v_es_1179_; size_t v___x_1180_; size_t v___x_1181_; lean_object* v_j_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v_es_1179_ = lean_ctor_get(v_x_1174_, 0);
v___x_1180_ = ((size_t)31ULL);
v___x_1181_ = lean_usize_land(v_x_1175_, v___x_1180_);
v_j_1182_ = lean_usize_to_nat(v___x_1181_);
v___x_1183_ = lean_array_get_size(v_es_1179_);
v___x_1184_ = lean_nat_dec_lt(v_j_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_dec(v_j_1182_);
lean_dec(v_x_1178_);
lean_dec(v_x_1177_);
return v_x_1174_;
}
else
{
lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1223_; 
lean_inc_ref(v_es_1179_);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v_x_1174_, 0);
lean_dec(v_unused_1224_);
v___x_1186_ = v_x_1174_;
v_isShared_1187_ = v_isSharedCheck_1223_;
goto v_resetjp_1185_;
}
else
{
lean_dec(v_x_1174_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1223_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_v_1188_; lean_object* v___x_1189_; lean_object* v_xs_x27_1190_; lean_object* v___y_1192_; 
v_v_1188_ = lean_array_fget(v_es_1179_, v_j_1182_);
v___x_1189_ = lean_box(0);
v_xs_x27_1190_ = lean_array_fset(v_es_1179_, v_j_1182_, v___x_1189_);
switch(lean_obj_tag(v_v_1188_))
{
case 0:
{
lean_object* v_key_1197_; lean_object* v_val_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1208_; 
v_key_1197_ = lean_ctor_get(v_v_1188_, 0);
v_val_1198_ = lean_ctor_get(v_v_1188_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_v_1188_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1200_ = v_v_1188_;
v_isShared_1201_ = v_isSharedCheck_1208_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_val_1198_);
lean_inc(v_key_1197_);
lean_dec(v_v_1188_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1208_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
uint8_t v___x_1202_; 
v___x_1202_ = l_Lean_instBEqMVarId_beq(v_x_1177_, v_key_1197_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_del_object(v___x_1200_);
v___x_1203_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1197_, v_val_1198_, v_x_1177_, v_x_1178_);
v___x_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
v___y_1192_ = v___x_1204_;
goto v___jp_1191_;
}
else
{
lean_object* v___x_1206_; 
lean_dec(v_val_1198_);
lean_dec(v_key_1197_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v_x_1178_);
lean_ctor_set(v___x_1200_, 0, v_x_1177_);
v___x_1206_ = v___x_1200_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_x_1177_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_x_1178_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
v___y_1192_ = v___x_1206_;
goto v___jp_1191_;
}
}
}
}
case 1:
{
lean_object* v_node_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1221_; 
v_node_1209_ = lean_ctor_get(v_v_1188_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_v_1188_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1211_ = v_v_1188_;
v_isShared_1212_ = v_isSharedCheck_1221_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_node_1209_);
lean_dec(v_v_1188_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1221_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
size_t v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1213_ = ((size_t)5ULL);
v___x_1214_ = lean_usize_shift_right(v_x_1175_, v___x_1213_);
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = lean_usize_add(v_x_1176_, v___x_1215_);
v___x_1217_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_node_1209_, v___x_1214_, v___x_1216_, v_x_1177_, v_x_1178_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v___x_1217_);
v___x_1219_ = v___x_1211_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
v___y_1192_ = v___x_1219_;
goto v___jp_1191_;
}
}
}
default: 
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_x_1177_);
lean_ctor_set(v___x_1222_, 1, v_x_1178_);
v___y_1192_ = v___x_1222_;
goto v___jp_1191_;
}
}
v___jp_1191_:
{
lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1193_ = lean_array_fset(v_xs_x27_1190_, v_j_1182_, v___y_1192_);
lean_dec(v_j_1182_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1193_);
v___x_1195_ = v___x_1186_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
else
{
lean_object* v_ks_1225_; lean_object* v_vs_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1244_; 
v_ks_1225_ = lean_ctor_get(v_x_1174_, 0);
v_vs_1226_ = lean_ctor_get(v_x_1174_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1228_ = v_x_1174_;
v_isShared_1229_ = v_isSharedCheck_1244_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_vs_1226_);
lean_inc(v_ks_1225_);
lean_dec(v_x_1174_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1244_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_ks_1225_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_vs_1226_);
v___x_1231_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v_newNode_1232_; size_t v___x_1233_; uint8_t v___x_1234_; 
v_newNode_1232_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20___redArg(v___x_1231_, v_x_1177_, v_x_1178_);
v___x_1233_ = ((size_t)7ULL);
v___x_1234_ = lean_usize_dec_le(v___x_1233_, v_x_1176_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1235_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1232_);
v___x_1236_ = lean_unsigned_to_nat(4u);
v___x_1237_ = lean_nat_dec_lt(v___x_1235_, v___x_1236_);
lean_dec(v___x_1235_);
if (v___x_1237_ == 0)
{
lean_object* v_ks_1238_; lean_object* v_vs_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_ks_1238_ = lean_ctor_get(v_newNode_1232_, 0);
lean_inc_ref(v_ks_1238_);
v_vs_1239_ = lean_ctor_get(v_newNode_1232_, 1);
lean_inc_ref(v_vs_1239_);
lean_dec_ref(v_newNode_1232_);
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0);
v___x_1242_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(v_x_1176_, v_ks_1238_, v_vs_1239_, v___x_1240_, v___x_1241_);
lean_dec_ref(v_vs_1239_);
lean_dec_ref(v_ks_1238_);
return v___x_1242_;
}
else
{
return v_newNode_1232_;
}
}
else
{
return v_newNode_1232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(size_t v_depth_1245_, lean_object* v_keys_1246_, lean_object* v_vals_1247_, lean_object* v_i_1248_, lean_object* v_entries_1249_){
_start:
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = lean_array_get_size(v_keys_1246_);
v___x_1251_ = lean_nat_dec_lt(v_i_1248_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec(v_i_1248_);
return v_entries_1249_;
}
else
{
lean_object* v_k_1252_; lean_object* v_v_1253_; uint64_t v___x_1254_; size_t v_h_1255_; size_t v___x_1256_; lean_object* v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; size_t v_h_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_k_1252_ = lean_array_fget_borrowed(v_keys_1246_, v_i_1248_);
v_v_1253_ = lean_array_fget_borrowed(v_vals_1247_, v_i_1248_);
v___x_1254_ = l_Lean_instHashableMVarId_hash(v_k_1252_);
v_h_1255_ = lean_uint64_to_usize(v___x_1254_);
v___x_1256_ = ((size_t)5ULL);
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = ((size_t)1ULL);
v___x_1259_ = lean_usize_sub(v_depth_1245_, v___x_1258_);
v___x_1260_ = lean_usize_mul(v___x_1256_, v___x_1259_);
v_h_1261_ = lean_usize_shift_right(v_h_1255_, v___x_1260_);
v___x_1262_ = lean_nat_add(v_i_1248_, v___x_1257_);
lean_dec(v_i_1248_);
lean_inc(v_v_1253_);
lean_inc(v_k_1252_);
v___x_1263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_entries_1249_, v_h_1261_, v_depth_1245_, v_k_1252_, v_v_1253_);
v_i_1248_ = v___x_1262_;
v_entries_1249_ = v___x_1263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg___boxed(lean_object* v_depth_1265_, lean_object* v_keys_1266_, lean_object* v_vals_1267_, lean_object* v_i_1268_, lean_object* v_entries_1269_){
_start:
{
size_t v_depth_boxed_1270_; lean_object* v_res_1271_; 
v_depth_boxed_1270_ = lean_unbox_usize(v_depth_1265_);
lean_dec(v_depth_1265_);
v_res_1271_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(v_depth_boxed_1270_, v_keys_1266_, v_vals_1267_, v_i_1268_, v_entries_1269_);
lean_dec_ref(v_vals_1267_);
lean_dec_ref(v_keys_1266_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___boxed(lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
size_t v_x_40209__boxed_1277_; size_t v_x_40210__boxed_1278_; lean_object* v_res_1279_; 
v_x_40209__boxed_1277_ = lean_unbox_usize(v_x_1273_);
lean_dec(v_x_1273_);
v_x_40210__boxed_1278_ = lean_unbox_usize(v_x_1274_);
lean_dec(v_x_1274_);
v_res_1279_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_x_1272_, v_x_40209__boxed_1277_, v_x_40210__boxed_1278_, v_x_1275_, v_x_1276_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
uint64_t v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v___x_1283_ = l_Lean_instHashableMVarId_hash(v_x_1281_);
v___x_1284_ = lean_uint64_to_usize(v___x_1283_);
v___x_1285_ = ((size_t)1ULL);
v___x_1286_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_x_1280_, v___x_1284_, v___x_1285_, v_x_1281_, v_x_1282_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(lean_object* v_mvarId_1287_, lean_object* v_val_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v_mctx_1292_; lean_object* v_cache_1293_; lean_object* v_zetaDeltaFVarIds_1294_; lean_object* v_postponed_1295_; lean_object* v_diag_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1325_; 
v___x_1291_ = lean_st_ref_take(v___y_1289_);
v_mctx_1292_ = lean_ctor_get(v___x_1291_, 0);
v_cache_1293_ = lean_ctor_get(v___x_1291_, 1);
v_zetaDeltaFVarIds_1294_ = lean_ctor_get(v___x_1291_, 2);
v_postponed_1295_ = lean_ctor_get(v___x_1291_, 3);
v_diag_1296_ = lean_ctor_get(v___x_1291_, 4);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1298_ = v___x_1291_;
v_isShared_1299_ = v_isSharedCheck_1325_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_diag_1296_);
lean_inc(v_postponed_1295_);
lean_inc(v_zetaDeltaFVarIds_1294_);
lean_inc(v_cache_1293_);
lean_inc(v_mctx_1292_);
lean_dec(v___x_1291_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1325_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v_depth_1300_; lean_object* v_levelAssignDepth_1301_; lean_object* v_lmvarCounter_1302_; lean_object* v_mvarCounter_1303_; lean_object* v_lDecls_1304_; lean_object* v_decls_1305_; lean_object* v_userNames_1306_; lean_object* v_lAssignment_1307_; lean_object* v_eAssignment_1308_; lean_object* v_dAssignment_1309_; lean_object* v_instanceTypedMVars_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1324_; 
v_depth_1300_ = lean_ctor_get(v_mctx_1292_, 0);
v_levelAssignDepth_1301_ = lean_ctor_get(v_mctx_1292_, 1);
v_lmvarCounter_1302_ = lean_ctor_get(v_mctx_1292_, 2);
v_mvarCounter_1303_ = lean_ctor_get(v_mctx_1292_, 3);
v_lDecls_1304_ = lean_ctor_get(v_mctx_1292_, 4);
v_decls_1305_ = lean_ctor_get(v_mctx_1292_, 5);
v_userNames_1306_ = lean_ctor_get(v_mctx_1292_, 6);
v_lAssignment_1307_ = lean_ctor_get(v_mctx_1292_, 7);
v_eAssignment_1308_ = lean_ctor_get(v_mctx_1292_, 8);
v_dAssignment_1309_ = lean_ctor_get(v_mctx_1292_, 9);
v_instanceTypedMVars_1310_ = lean_ctor_get(v_mctx_1292_, 10);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_mctx_1292_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1312_ = v_mctx_1292_;
v_isShared_1313_ = v_isSharedCheck_1324_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_instanceTypedMVars_1310_);
lean_inc(v_dAssignment_1309_);
lean_inc(v_eAssignment_1308_);
lean_inc(v_lAssignment_1307_);
lean_inc(v_userNames_1306_);
lean_inc(v_decls_1305_);
lean_inc(v_lDecls_1304_);
lean_inc(v_mvarCounter_1303_);
lean_inc(v_lmvarCounter_1302_);
lean_inc(v_levelAssignDepth_1301_);
lean_inc(v_depth_1300_);
lean_dec(v_mctx_1292_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1324_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(v_eAssignment_1308_, v_mvarId_1287_, v_val_1288_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 8, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_depth_1300_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_levelAssignDepth_1301_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_lmvarCounter_1302_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_mvarCounter_1303_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_lDecls_1304_);
lean_ctor_set(v_reuseFailAlloc_1323_, 5, v_decls_1305_);
lean_ctor_set(v_reuseFailAlloc_1323_, 6, v_userNames_1306_);
lean_ctor_set(v_reuseFailAlloc_1323_, 7, v_lAssignment_1307_);
lean_ctor_set(v_reuseFailAlloc_1323_, 8, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1323_, 9, v_dAssignment_1309_);
lean_ctor_set(v_reuseFailAlloc_1323_, 10, v_instanceTypedMVars_1310_);
v___x_1316_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1318_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1316_);
v___x_1318_ = v___x_1298_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_cache_1293_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_zetaDeltaFVarIds_1294_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v_postponed_1295_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_diag_1296_);
v___x_1318_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = lean_st_ref_put(v___y_1289_, v___x_1318_);
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___boxed(lean_object* v_mvarId_1326_, lean_object* v_val_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v_mvarId_1326_, v_val_1327_, v___y_1328_);
lean_dec(v___y_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
if (lean_obj_tag(v_a_1331_) == 0)
{
lean_object* v___x_1333_; 
v___x_1333_ = l_List_reverse___redArg(v_a_1332_);
return v___x_1333_;
}
else
{
lean_object* v_head_1334_; lean_object* v_snd_1335_; lean_object* v_tail_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1359_; 
v_head_1334_ = lean_ctor_get(v_a_1331_, 0);
lean_inc(v_head_1334_);
v_snd_1335_ = lean_ctor_get(v_head_1334_, 1);
lean_inc(v_snd_1335_);
v_tail_1336_ = lean_ctor_get(v_a_1331_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_a_1331_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; 
v_unused_1360_ = lean_ctor_get(v_a_1331_, 0);
lean_dec(v_unused_1360_);
v___x_1338_ = v_a_1331_;
v_isShared_1339_ = v_isSharedCheck_1359_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_tail_1336_);
lean_dec(v_a_1331_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1359_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_fst_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1357_; 
v_fst_1340_ = lean_ctor_get(v_head_1334_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_head_1334_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; 
v_unused_1358_ = lean_ctor_get(v_head_1334_, 1);
lean_dec(v_unused_1358_);
v___x_1342_ = v_head_1334_;
v_isShared_1343_ = v_isSharedCheck_1357_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_fst_1340_);
lean_dec(v_head_1334_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1357_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_width_1344_; lean_object* v_atomNumber_1345_; uint8_t v_synthetic_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v_width_1344_ = lean_ctor_get(v_snd_1335_, 0);
lean_inc(v_width_1344_);
v_atomNumber_1345_ = lean_ctor_get(v_snd_1335_, 1);
lean_inc(v_atomNumber_1345_);
v_synthetic_1346_ = lean_ctor_get_uint8(v_snd_1335_, sizeof(void*)*2);
lean_dec(v_snd_1335_);
v___x_1347_ = lean_box(v_synthetic_1346_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v___x_1347_);
v___x_1349_ = v___x_1342_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_fst_1340_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_width_1344_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_atomNumber_1345_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 1, v_a_1332_);
lean_ctor_set(v___x_1338_, 0, v___x_1351_);
v___x_1353_ = v___x_1338_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_a_1332_);
v___x_1353_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
v_a_1331_ = v_tail_1336_;
v_a_1332_ = v___x_1353_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(lean_object* v_cls_1364_, lean_object* v_msg_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_ref_1371_; lean_object* v___x_1372_; lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1417_; 
v_ref_1371_ = lean_ctor_get(v___y_1368_, 2);
v___x_1372_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1417_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1417_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v_traceState_1378_; lean_object* v_env_1379_; lean_object* v_nextMacroScope_1380_; lean_object* v_ngen_1381_; lean_object* v_auxDeclNGen_1382_; lean_object* v_cache_1383_; lean_object* v_messages_1384_; lean_object* v_infoState_1385_; lean_object* v_snapshotTasks_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1416_; 
v___x_1377_ = lean_st_ref_take(v___y_1369_);
v_traceState_1378_ = lean_ctor_get(v___x_1377_, 4);
v_env_1379_ = lean_ctor_get(v___x_1377_, 0);
v_nextMacroScope_1380_ = lean_ctor_get(v___x_1377_, 1);
v_ngen_1381_ = lean_ctor_get(v___x_1377_, 2);
v_auxDeclNGen_1382_ = lean_ctor_get(v___x_1377_, 3);
v_cache_1383_ = lean_ctor_get(v___x_1377_, 5);
v_messages_1384_ = lean_ctor_get(v___x_1377_, 6);
v_infoState_1385_ = lean_ctor_get(v___x_1377_, 7);
v_snapshotTasks_1386_ = lean_ctor_get(v___x_1377_, 8);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1388_ = v___x_1377_;
v_isShared_1389_ = v_isSharedCheck_1416_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_snapshotTasks_1386_);
lean_inc(v_infoState_1385_);
lean_inc(v_messages_1384_);
lean_inc(v_cache_1383_);
lean_inc(v_traceState_1378_);
lean_inc(v_auxDeclNGen_1382_);
lean_inc(v_ngen_1381_);
lean_inc(v_nextMacroScope_1380_);
lean_inc(v_env_1379_);
lean_dec(v___x_1377_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1416_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
uint64_t v_tid_1390_; lean_object* v_traces_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1415_; 
v_tid_1390_ = lean_ctor_get_uint64(v_traceState_1378_, sizeof(void*)*1);
v_traces_1391_ = lean_ctor_get(v_traceState_1378_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_traceState_1378_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1393_ = v_traceState_1378_;
v_isShared_1394_ = v_isSharedCheck_1415_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_traces_1391_);
lean_dec(v_traceState_1378_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1415_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; double v___x_1396_; uint8_t v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1395_ = lean_box(0);
v___x_1396_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0);
v___x_1397_ = 0;
v___x_1398_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0));
v___x_1399_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1399_, 0, v_cls_1364_);
lean_ctor_set(v___x_1399_, 1, v___x_1395_);
lean_ctor_set(v___x_1399_, 2, v___x_1398_);
lean_ctor_set_float(v___x_1399_, sizeof(void*)*3, v___x_1396_);
lean_ctor_set_float(v___x_1399_, sizeof(void*)*3 + 8, v___x_1396_);
lean_ctor_set_uint8(v___x_1399_, sizeof(void*)*3 + 16, v___x_1397_);
v___x_1400_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1));
v___x_1401_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1399_);
lean_ctor_set(v___x_1401_, 1, v_a_1373_);
lean_ctor_set(v___x_1401_, 2, v___x_1400_);
lean_inc(v_ref_1371_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_ref_1371_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = l_Lean_PersistentArray_push___redArg(v_traces_1391_, v___x_1402_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1403_);
v___x_1405_ = v___x_1393_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1403_);
lean_ctor_set_uint64(v_reuseFailAlloc_1414_, sizeof(void*)*1, v_tid_1390_);
v___x_1405_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1407_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 4, v___x_1405_);
v___x_1407_ = v___x_1388_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_env_1379_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_nextMacroScope_1380_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_ngen_1381_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v_auxDeclNGen_1382_);
lean_ctor_set(v_reuseFailAlloc_1413_, 4, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1413_, 5, v_cache_1383_);
lean_ctor_set(v_reuseFailAlloc_1413_, 6, v_messages_1384_);
lean_ctor_set(v_reuseFailAlloc_1413_, 7, v_infoState_1385_);
lean_ctor_set(v_reuseFailAlloc_1413_, 8, v_snapshotTasks_1386_);
v___x_1407_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1408_ = lean_st_ref_put(v___y_1369_, v___x_1407_);
v___x_1409_ = lean_box(0);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1409_);
v___x_1411_ = v___x_1375_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___boxed(lean_object* v_cls_1418_, lean_object* v_msg_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(v_cls_1418_, v_msg_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1425_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_box(0);
v___x_1427_ = lean_unsigned_to_nat(16u);
v___x_1428_ = lean_mk_array(v___x_1427_, v___x_1426_);
return v___x_1428_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1429_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___x_1429_);
return v___x_1431_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4));
v___x_1437_ = l_Lean_stringToMessageData(v___x_1436_);
return v___x_1437_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1438_; double v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(1000000000u);
v___x_1439_ = lean_float_of_nat(v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(lean_object* v_unsatProver_1440_, lean_object* v_g_1441_, lean_object* v_cls_1442_, uint8_t v___x_1443_, lean_object* v___x_1444_, lean_object* v___f_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v_toCold_1545_; lean_object* v_options_1546_; lean_object* v_inheritedTraceOptions_1547_; uint8_t v_hasTrace_1548_; lean_object* v___y_1550_; 
v_toCold_1545_ = lean_ctor_get(v___y_1452_, 0);
v_options_1546_ = lean_ctor_get(v_toCold_1545_, 2);
v_inheritedTraceOptions_1547_ = lean_ctor_get(v_toCold_1545_, 11);
v_hasTrace_1548_ = lean_ctor_get_uint8(v_options_1546_, sizeof(void*)*1);
if (v_hasTrace_1548_ == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref(v___f_1445_);
lean_dec_ref(v___x_1444_);
lean_inc(v_g_1441_);
v___x_1579_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1441_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
v___y_1550_ = v___x_1579_;
goto v___jp_1549_;
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v_a_1586_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v_a_1601_; 
v___x_1580_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3));
lean_inc(v_cls_1442_);
v___x_1581_ = l_Lean_Name_append(v___x_1580_, v_cls_1442_);
v___x_1582_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1547_, v_options_1546_, v___x_1581_);
lean_dec(v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = l_Lean_trace_profiler;
v___x_1652_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_options_1546_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
lean_dec_ref(v___f_1445_);
lean_dec_ref(v___x_1444_);
lean_inc(v_g_1441_);
v___x_1653_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1441_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
v___y_1550_ = v___x_1653_;
goto v___jp_1549_;
}
else
{
goto v___jp_1610_;
}
}
else
{
goto v___jp_1610_;
}
v___jp_1583_:
{
lean_object* v___x_1587_; double v___x_1588_; double v___x_1589_; double v___x_1590_; double v___x_1591_; double v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1587_ = lean_io_mono_nanos_now();
v___x_1588_ = lean_float_of_nat(v___y_1585_);
v___x_1589_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6);
v___x_1590_ = lean_float_div(v___x_1588_, v___x_1589_);
v___x_1591_ = lean_float_of_nat(v___x_1587_);
v___x_1592_ = lean_float_div(v___x_1591_, v___x_1589_);
v___x_1593_ = lean_box_float(v___x_1590_);
v___x_1594_ = lean_box_float(v___x_1592_);
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v_a_1586_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
lean_inc(v_cls_1442_);
v___x_1597_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(v_cls_1442_, v___x_1443_, v___x_1444_, v_options_1546_, v___x_1582_, v___y_1584_, v___f_1445_, v___x_1596_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
v___y_1550_ = v___x_1597_;
goto v___jp_1549_;
}
v___jp_1598_:
{
lean_object* v___x_1602_; double v___x_1603_; double v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1602_ = lean_io_get_num_heartbeats();
v___x_1603_ = lean_float_of_nat(v___y_1599_);
v___x_1604_ = lean_float_of_nat(v___x_1602_);
v___x_1605_ = lean_box_float(v___x_1603_);
v___x_1606_ = lean_box_float(v___x_1604_);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1605_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v_a_1601_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
lean_inc(v_cls_1442_);
v___x_1609_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(v_cls_1442_, v___x_1443_, v___x_1444_, v_options_1546_, v___x_1582_, v___y_1600_, v___f_1445_, v___x_1608_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
v___y_1550_ = v___x_1609_;
goto v___jp_1549_;
}
v___jp_1610_:
{
lean_object* v___x_1611_; lean_object* v_a_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1611_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(v___y_1453_);
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref(v___x_1611_);
v___x_1613_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1614_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_options_1546_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = lean_io_mono_nanos_now();
lean_inc(v_g_1441_);
v___x_1616_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1441_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set_tag(v___x_1619_, 1);
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
v___y_1584_ = v_a_1612_;
v___y_1585_ = v___x_1615_;
v_a_1586_ = v___x_1622_;
goto v___jp_1583_;
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
v_a_1625_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1616_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1616_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set_tag(v___x_1627_, 0);
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
v___y_1584_ = v_a_1612_;
v___y_1585_ = v___x_1615_;
v_a_1586_ = v___x_1630_;
goto v___jp_1583_;
}
}
}
}
else
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = lean_io_get_num_heartbeats();
lean_inc(v_g_1441_);
v___x_1634_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1441_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set_tag(v___x_1637_, 1);
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
v___y_1599_ = v___x_1633_;
v___y_1600_ = v_a_1612_;
v_a_1601_ = v___x_1640_;
goto v___jp_1598_;
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1634_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1634_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 0);
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
v___y_1599_ = v___x_1633_;
v___y_1600_ = v_a_1612_;
v_a_1601_ = v___x_1648_;
goto v___jp_1598_;
}
}
}
}
}
}
v___jp_1455_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1466_ = lean_box(0);
v___x_1467_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v___y_1465_, v___x_1466_);
v___x_1468_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1);
v___x_1469_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v___x_1467_, v___x_1468_);
lean_dec(v___x_1467_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1462_);
lean_inc_ref(v___y_1457_);
lean_inc(v_g_1441_);
v___x_1470_ = lean_apply_8(v_unsatProver_1440_, v_g_1441_, v___y_1457_, v___x_1469_, v___y_1462_, v___y_1464_, v___y_1458_, v___y_1463_, lean_box(0));
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1516_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1516_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1516_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
if (lean_obj_tag(v_a_1471_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref(v___y_1457_);
lean_dec(v_g_1441_);
v_a_1475_ = lean_ctor_get(v_a_1471_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_a_1471_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1477_ = v_a_1471_;
v_isShared_1478_ = v_isSharedCheck_1485_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v_a_1471_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1485_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1482_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1480_);
v___x_1482_ = v___x_1473_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1515_; 
lean_del_object(v___x_1473_);
v_a_1486_ = lean_ctor_get(v_a_1471_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_a_1471_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1488_ = v_a_1471_;
v_isShared_1489_ = v_isSharedCheck_1515_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v_a_1471_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1515_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_proof_1490_; lean_object* v_cert_1491_; lean_object* v_proveFalse_1492_; lean_object* v___x_1493_; 
v_proof_1490_ = lean_ctor_get(v_a_1486_, 0);
lean_inc_ref(v_proof_1490_);
v_cert_1491_ = lean_ctor_get(v_a_1486_, 1);
lean_inc(v_cert_1491_);
lean_dec(v_a_1486_);
v_proveFalse_1492_ = lean_ctor_get(v___y_1457_, 1);
lean_inc_ref(v_proveFalse_1492_);
lean_dec_ref(v___y_1457_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1462_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1456_);
lean_inc_ref(v___y_1461_);
v___x_1493_ = lean_apply_10(v_proveFalse_1492_, v_proof_1490_, v___y_1461_, v___y_1456_, v___y_1460_, v___y_1459_, v___y_1462_, v___y_1464_, v___y_1458_, v___y_1463_, lean_box(0));
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1505_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v___x_1495_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v_g_1441_, v_a_1494_, v___y_1464_);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v___x_1495_, 0);
lean_dec(v_unused_1506_);
v___x_1497_ = v___x_1495_;
v_isShared_1498_ = v_isSharedCheck_1505_;
goto v_resetjp_1496_;
}
else
{
lean_dec(v___x_1495_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1505_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v_cert_1491_);
v___x_1500_ = v___x_1488_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_cert_1491_);
v___x_1500_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1502_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1500_);
v___x_1502_ = v___x_1497_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec(v_cert_1491_);
lean_del_object(v___x_1488_);
lean_dec(v_g_1441_);
v_a_1507_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1493_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1493_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
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
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec_ref(v___y_1457_);
lean_dec(v_g_1441_);
v_a_1517_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1470_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1470_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
v___jp_1525_:
{
lean_object* v___x_1535_; lean_object* v_atoms_1536_; lean_object* v_buckets_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1535_ = lean_st_ref_get(v___y_1528_);
v_atoms_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc_ref(v_atoms_1536_);
lean_dec(v___x_1535_);
v_buckets_1537_ = lean_ctor_get(v_atoms_1536_, 1);
lean_inc_ref(v_buckets_1537_);
lean_dec_ref(v_atoms_1536_);
v___x_1538_ = lean_box(0);
v___x_1539_ = lean_array_get_size(v_buckets_1537_);
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = lean_nat_dec_lt(v___x_1540_, v___x_1539_);
if (v___x_1541_ == 0)
{
lean_dec_ref(v_buckets_1537_);
v___y_1456_ = v___y_1528_;
v___y_1457_ = v___y_1526_;
v___y_1458_ = v___y_1533_;
v___y_1459_ = v___y_1530_;
v___y_1460_ = v___y_1529_;
v___y_1461_ = v___y_1527_;
v___y_1462_ = v___y_1531_;
v___y_1463_ = v___y_1534_;
v___y_1464_ = v___y_1532_;
v___y_1465_ = v___x_1538_;
goto v___jp_1455_;
}
else
{
size_t v___x_1542_; size_t v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = lean_usize_of_nat(v___x_1539_);
v___x_1543_ = ((size_t)0ULL);
v___x_1544_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_buckets_1537_, v___x_1542_, v___x_1543_, v___x_1538_);
lean_dec_ref(v_buckets_1537_);
v___y_1456_ = v___y_1528_;
v___y_1457_ = v___y_1526_;
v___y_1458_ = v___y_1533_;
v___y_1459_ = v___y_1530_;
v___y_1460_ = v___y_1529_;
v___y_1461_ = v___y_1527_;
v___y_1462_ = v___y_1531_;
v___y_1463_ = v___y_1534_;
v___y_1464_ = v___y_1532_;
v___y_1465_ = v___x_1544_;
goto v___jp_1455_;
}
}
v___jp_1549_:
{
if (lean_obj_tag(v___y_1550_) == 0)
{
if (v_hasTrace_1548_ == 0)
{
lean_object* v_a_1551_; 
lean_dec(v_cls_1442_);
v_a_1551_ = lean_ctor_get(v___y_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___y_1550_, 1);
v___y_1526_ = v_a_1551_;
v___y_1527_ = v___y_1446_;
v___y_1528_ = v___y_1447_;
v___y_1529_ = v___y_1448_;
v___y_1530_ = v___y_1449_;
v___y_1531_ = v___y_1450_;
v___y_1532_ = v___y_1451_;
v___y_1533_ = v___y_1452_;
v___y_1534_ = v___y_1453_;
goto v___jp_1525_;
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v_a_1552_ = lean_ctor_get(v___y_1550_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___y_1550_, 1);
v___x_1553_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3));
lean_inc(v_cls_1442_);
v___x_1554_ = l_Lean_Name_append(v___x_1553_, v_cls_1442_);
v___x_1555_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1547_, v_options_1546_, v___x_1554_);
lean_dec(v___x_1554_);
if (v___x_1555_ == 0)
{
lean_dec(v_cls_1442_);
v___y_1526_ = v_a_1552_;
v___y_1527_ = v___y_1446_;
v___y_1528_ = v___y_1447_;
v___y_1529_ = v___y_1448_;
v___y_1530_ = v___y_1449_;
v___y_1531_ = v___y_1450_;
v___y_1532_ = v___y_1451_;
v___y_1533_ = v___y_1452_;
v___y_1534_ = v___y_1453_;
goto v___jp_1525_;
}
else
{
lean_object* v_bvExpr_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_bvExpr_1556_ = lean_ctor_get(v_a_1552_, 0);
v___x_1557_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5);
lean_inc_ref(v_bvExpr_1556_);
v___x_1558_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_bvExpr_1556_);
v___x_1559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
v___x_1560_ = l_Lean_MessageData_ofFormat(v___x_1559_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1557_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(v_cls_1442_, v___x_1561_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_dec_ref_known(v___x_1562_, 1);
v___y_1526_ = v_a_1552_;
v___y_1527_ = v___y_1446_;
v___y_1528_ = v___y_1447_;
v___y_1529_ = v___y_1448_;
v___y_1530_ = v___y_1449_;
v___y_1531_ = v___y_1450_;
v___y_1532_ = v___y_1451_;
v___y_1533_ = v___y_1452_;
v___y_1534_ = v___y_1453_;
goto v___jp_1525_;
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_a_1552_);
lean_dec(v_g_1441_);
lean_dec_ref(v_unsatProver_1440_);
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_cls_1442_);
lean_dec(v_g_1441_);
lean_dec_ref(v_unsatProver_1440_);
v_a_1571_ = lean_ctor_get(v___y_1550_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___y_1550_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___y_1550_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___y_1550_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed(lean_object* v_unsatProver_1654_, lean_object* v_g_1655_, lean_object* v_cls_1656_, lean_object* v___x_1657_, lean_object* v___x_1658_, lean_object* v___f_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
uint8_t v___x_40608__boxed_1669_; lean_object* v_res_1670_; 
v___x_40608__boxed_1669_ = lean_unbox(v___x_1657_);
v_res_1670_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(v_unsatProver_1654_, v_g_1655_, v_cls_1656_, v___x_40608__boxed_1669_, v___x_1658_, v___f_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(lean_object* v_g_1679_, lean_object* v_unsatProver_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v___f_1690_; lean_object* v_cls_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___f_1695_; lean_object* v___x_1696_; 
v___f_1690_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0));
v_cls_1691_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4));
v___x_1692_ = 1;
v___x_1693_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0));
v___x_1694_ = lean_box(v___x_1692_);
lean_inc(v_g_1679_);
v___f_1695_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed), 15, 6);
lean_closure_set(v___f_1695_, 0, v_unsatProver_1680_);
lean_closure_set(v___f_1695_, 1, v_g_1679_);
lean_closure_set(v___f_1695_, 2, v_cls_1691_);
lean_closure_set(v___f_1695_, 3, v___x_1694_);
lean_closure_set(v___f_1695_, 4, v___x_1693_);
lean_closure_set(v___f_1695_, 5, v___f_1690_);
v___x_1696_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_g_1679_, v___f_1695_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___boxed(lean_object* v_g_1697_, lean_object* v_unsatProver_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1697_, v_unsatProver_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(lean_object* v_00_u03b1_1709_, lean_object* v_g_1710_, lean_object* v_unsatProver_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1710_, v_unsatProver_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_g_1723_, lean_object* v_unsatProver_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(v_00_u03b1_1722_, v_g_1723_, v_unsatProver_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(lean_object* v_mvarId_1735_, lean_object* v_val_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v_mvarId_1735_, v_val_1736_, v___y_1742_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___boxed(lean_object* v_mvarId_1747_, lean_object* v_val_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(v_mvarId_1747_, v_val_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6(lean_object* v_cls_1759_, lean_object* v_msg_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(v_cls_1759_, v_msg_1760_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___boxed(lean_object* v_cls_1771_, lean_object* v_msg_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6(v_cls_1771_, v_msg_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13(lean_object* v_00_u03b1_1783_, lean_object* v_x_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_x_1784_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1795_, lean_object* v_x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13(v_00_u03b1_1795_, v_x_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1(lean_object* v_00_u03b2_1807_, lean_object* v_m_1808_, lean_object* v_a_1809_, lean_object* v_b_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1___redArg(v_m_1808_, v_a_1809_, v_b_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2(lean_object* v_as_1812_, lean_object* v_as_x27_1813_, lean_object* v_b_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v_as_x27_1813_, v_b_1814_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___boxed(lean_object* v_as_1817_, lean_object* v_as_x27_1818_, lean_object* v_b_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2(v_as_1817_, v_as_x27_1818_, v_b_1819_, v_a_1820_);
lean_dec(v_as_x27_1818_);
lean_dec(v_as_1817_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4(lean_object* v_00_u03b2_1822_, lean_object* v_x_1823_, lean_object* v_x_1824_, lean_object* v_x_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(v_x_1823_, v_x_1824_, v_x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12(lean_object* v_oldTraces_1827_, lean_object* v_data_1828_, lean_object* v_ref_1829_, lean_object* v_msg_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg(v_oldTraces_1827_, v_data_1828_, v_ref_1829_, v_msg_1830_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___boxed(lean_object* v_oldTraces_1841_, lean_object* v_data_1842_, lean_object* v_ref_1843_, lean_object* v_msg_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12(v_oldTraces_1841_, v_data_1842_, v_ref_1843_, v_msg_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
return v_res_1854_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_1855_, lean_object* v_a_1856_, lean_object* v_x_1857_){
_start:
{
uint8_t v___x_1858_; 
v___x_1858_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(v_a_1856_, v_x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1859_, lean_object* v_a_1860_, lean_object* v_x_1861_){
_start:
{
uint8_t v_res_1862_; lean_object* v_r_1863_; 
v_res_1862_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4(v_00_u03b2_1859_, v_a_1860_, v_x_1861_);
lean_dec(v_x_1861_);
lean_dec(v_a_1860_);
v_r_1863_ = lean_box(v_res_1862_);
return v_r_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_1864_, lean_object* v_data_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5___redArg(v_data_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_1867_, lean_object* v_a_1868_, lean_object* v_b_1869_, lean_object* v_x_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(v_a_1868_, v_b_1869_, v_x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10(lean_object* v_00_u03b2_1872_, lean_object* v_x_1873_, size_t v_x_1874_, size_t v_x_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_x_1873_, v_x_1874_, v_x_1875_, v_x_1876_, v_x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___boxed(lean_object* v_00_u03b2_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
size_t v_x_41239__boxed_1885_; size_t v_x_41240__boxed_1886_; lean_object* v_res_1887_; 
v_x_41239__boxed_1885_ = lean_unbox_usize(v_x_1881_);
lean_dec(v_x_1881_);
v_x_41240__boxed_1886_ = lean_unbox_usize(v_x_1882_);
lean_dec(v_x_1882_);
v_res_1887_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10(v_00_u03b2_1879_, v_x_1880_, v_x_41239__boxed_1885_, v_x_41240__boxed_1886_, v_x_1883_, v_x_1884_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15(lean_object* v_00_u03b2_1888_, lean_object* v_i_1889_, lean_object* v_source_1890_, lean_object* v_target_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15___redArg(v_i_1889_, v_source_1890_, v_target_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20(lean_object* v_00_u03b2_1893_, lean_object* v_n_1894_, lean_object* v_k_1895_, lean_object* v_v_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20___redArg(v_n_1894_, v_k_1895_, v_v_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21(lean_object* v_00_u03b2_1898_, size_t v_depth_1899_, lean_object* v_keys_1900_, lean_object* v_vals_1901_, lean_object* v_heq_1902_, lean_object* v_i_1903_, lean_object* v_entries_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(v_depth_1899_, v_keys_1900_, v_vals_1901_, v_i_1903_, v_entries_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___boxed(lean_object* v_00_u03b2_1906_, lean_object* v_depth_1907_, lean_object* v_keys_1908_, lean_object* v_vals_1909_, lean_object* v_heq_1910_, lean_object* v_i_1911_, lean_object* v_entries_1912_){
_start:
{
size_t v_depth_boxed_1913_; lean_object* v_res_1914_; 
v_depth_boxed_1913_ = lean_unbox_usize(v_depth_1907_);
lean_dec(v_depth_1907_);
v_res_1914_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21(v_00_u03b2_1906_, v_depth_boxed_1913_, v_keys_1908_, v_vals_1909_, v_heq_1910_, v_i_1911_, v_entries_1912_);
lean_dec_ref(v_vals_1909_);
lean_dec_ref(v_keys_1908_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19(lean_object* v_00_u03b2_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19___redArg(v_x_1916_, v_x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23(lean_object* v_00_u03b2_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23___redArg(v_x_1920_, v_x_1921_, v_x_1922_, v_x_1923_);
return v___x_1924_;
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
