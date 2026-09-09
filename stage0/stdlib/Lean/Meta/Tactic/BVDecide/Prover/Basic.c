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
lean_object* v___x_88_; lean_object* v_env_89_; lean_object* v___x_90_; lean_object* v_mctx_91_; lean_object* v_lctx_92_; lean_object* v_options_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_88_ = lean_st_ref_get(v___y_86_);
v_env_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc_ref(v_env_89_);
lean_dec(v___x_88_);
v___x_90_ = lean_st_ref_get(v___y_84_);
v_mctx_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc_ref(v_mctx_91_);
lean_dec(v___x_90_);
v_lctx_92_ = lean_ctor_get(v___y_83_, 2);
v_options_93_ = lean_ctor_get(v___y_85_, 1);
lean_inc_ref(v_options_93_);
lean_inc_ref(v_lctx_92_);
v___x_94_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_94_, 0, v_env_89_);
lean_ctor_set(v___x_94_, 1, v_mctx_91_);
lean_ctor_set(v___x_94_, 2, v_lctx_92_);
lean_ctor_set(v___x_94_, 3, v_options_93_);
v___x_95_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v_msgData_82_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5___boxed(lean_object* v_msgData_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msgData_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(lean_object* v_msg_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_ref_110_; lean_object* v___x_111_; lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_120_; 
v_ref_110_ = lean_ctor_get(v___y_107_, 4);
v___x_111_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_120_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_118_; 
lean_inc(v_ref_110_);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v_ref_110_);
lean_ctor_set(v___x_116_, 1, v_a_112_);
if (v_isShared_115_ == 0)
{
lean_ctor_set_tag(v___x_114_, 1);
lean_ctor_set(v___x_114_, 0, v___x_116_);
v___x_118_ = v___x_114_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg___boxed(lean_object* v_msg_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_127_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(lean_object* v_a_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
else
{
lean_object* v_key_131_; lean_object* v_tail_132_; lean_object* v_type_133_; lean_object* v_type_134_; uint8_t v___x_135_; 
v_key_131_ = lean_ctor_get(v_x_129_, 0);
v_tail_132_ = lean_ctor_get(v_x_129_, 2);
v_type_133_ = lean_ctor_get(v_key_131_, 1);
v_type_134_ = lean_ctor_get(v_a_128_, 1);
v___x_135_ = lean_expr_eqv(v_type_133_, v_type_134_);
if (v___x_135_ == 0)
{
v_x_129_ = v_tail_132_;
goto _start;
}
else
{
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg___boxed(lean_object* v_a_137_, lean_object* v_x_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_137_, v_x_138_);
lean_dec(v_x_138_);
lean_dec_ref(v_a_137_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
return v_x_141_;
}
else
{
lean_object* v_key_143_; lean_object* v_value_144_; lean_object* v_tail_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_169_; 
v_key_143_ = lean_ctor_get(v_x_142_, 0);
v_value_144_ = lean_ctor_get(v_x_142_, 1);
v_tail_145_ = lean_ctor_get(v_x_142_, 2);
v_isSharedCheck_169_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_169_ == 0)
{
v___x_147_ = v_x_142_;
v_isShared_148_ = v_isSharedCheck_169_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_tail_145_);
lean_inc(v_value_144_);
lean_inc(v_key_143_);
lean_dec(v_x_142_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_169_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_type_149_; lean_object* v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint64_t v_fold_154_; uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v___x_157_; size_t v___x_158_; size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
v_type_149_ = lean_ctor_get(v_key_143_, 1);
v___x_150_ = lean_array_get_size(v_x_141_);
v___x_151_ = l_Lean_Expr_hash(v_type_149_);
v___x_152_ = 32ULL;
v___x_153_ = lean_uint64_shift_right(v___x_151_, v___x_152_);
v_fold_154_ = lean_uint64_xor(v___x_151_, v___x_153_);
v___x_155_ = 16ULL;
v___x_156_ = lean_uint64_shift_right(v_fold_154_, v___x_155_);
v___x_157_ = lean_uint64_xor(v_fold_154_, v___x_156_);
v___x_158_ = lean_uint64_to_usize(v___x_157_);
v___x_159_ = lean_usize_of_nat(v___x_150_);
v___x_160_ = ((size_t)1ULL);
v___x_161_ = lean_usize_sub(v___x_159_, v___x_160_);
v___x_162_ = lean_usize_land(v___x_158_, v___x_161_);
v___x_163_ = lean_array_uget_borrowed(v_x_141_, v___x_162_);
lean_inc(v___x_163_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 2, v___x_163_);
v___x_165_ = v___x_147_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_key_143_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_value_144_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v___x_163_);
v___x_165_ = v_reuseFailAlloc_168_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; 
v___x_166_ = lean_array_uset(v_x_141_, v___x_162_, v___x_165_);
v_x_141_ = v___x_166_;
v_x_142_ = v_tail_145_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(lean_object* v_i_170_, lean_object* v_source_171_, lean_object* v_target_172_){
_start:
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = lean_array_get_size(v_source_171_);
v___x_174_ = lean_nat_dec_lt(v_i_170_, v___x_173_);
if (v___x_174_ == 0)
{
lean_dec_ref(v_source_171_);
lean_dec(v_i_170_);
return v_target_172_;
}
else
{
lean_object* v_es_175_; lean_object* v___x_176_; lean_object* v_source_177_; lean_object* v_target_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_es_175_ = lean_array_fget(v_source_171_, v_i_170_);
v___x_176_ = lean_box(0);
v_source_177_ = lean_array_fset(v_source_171_, v_i_170_, v___x_176_);
v_target_178_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(v_target_172_, v_es_175_);
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_nat_add(v_i_170_, v___x_179_);
lean_dec(v_i_170_);
v_i_170_ = v___x_180_;
v_source_171_ = v_source_177_;
v_target_172_ = v_target_178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(lean_object* v_data_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v_nbuckets_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_183_ = lean_array_get_size(v_data_182_);
v___x_184_ = lean_unsigned_to_nat(2u);
v_nbuckets_185_ = lean_nat_mul(v___x_183_, v___x_184_);
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = lean_box(0);
v___x_188_ = lean_mk_array(v_nbuckets_185_, v___x_187_);
v___x_189_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v___x_186_, v_data_182_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(lean_object* v_m_190_, lean_object* v_a_191_, lean_object* v_b_192_){
_start:
{
lean_object* v_size_193_; lean_object* v_buckets_194_; lean_object* v_type_195_; lean_object* v___x_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; uint64_t v_fold_200_; uint64_t v___x_201_; uint64_t v___x_202_; uint64_t v___x_203_; size_t v___x_204_; size_t v___x_205_; size_t v___x_206_; size_t v___x_207_; size_t v___x_208_; lean_object* v_bkt_209_; uint8_t v___x_210_; 
v_size_193_ = lean_ctor_get(v_m_190_, 0);
v_buckets_194_ = lean_ctor_get(v_m_190_, 1);
v_type_195_ = lean_ctor_get(v_a_191_, 1);
v___x_196_ = lean_array_get_size(v_buckets_194_);
v___x_197_ = l_Lean_Expr_hash(v_type_195_);
v___x_198_ = 32ULL;
v___x_199_ = lean_uint64_shift_right(v___x_197_, v___x_198_);
v_fold_200_ = lean_uint64_xor(v___x_197_, v___x_199_);
v___x_201_ = 16ULL;
v___x_202_ = lean_uint64_shift_right(v_fold_200_, v___x_201_);
v___x_203_ = lean_uint64_xor(v_fold_200_, v___x_202_);
v___x_204_ = lean_uint64_to_usize(v___x_203_);
v___x_205_ = lean_usize_of_nat(v___x_196_);
v___x_206_ = ((size_t)1ULL);
v___x_207_ = lean_usize_sub(v___x_205_, v___x_206_);
v___x_208_ = lean_usize_land(v___x_204_, v___x_207_);
v_bkt_209_ = lean_array_uget_borrowed(v_buckets_194_, v___x_208_);
v___x_210_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_191_, v_bkt_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_231_; 
lean_inc_ref(v_buckets_194_);
lean_inc(v_size_193_);
v_isSharedCheck_231_ = !lean_is_exclusive(v_m_190_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; lean_object* v_unused_233_; 
v_unused_232_ = lean_ctor_get(v_m_190_, 1);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_m_190_, 0);
lean_dec(v_unused_233_);
v___x_212_ = v_m_190_;
v_isShared_213_ = v_isSharedCheck_231_;
goto v_resetjp_211_;
}
else
{
lean_dec(v_m_190_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_231_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v_size_x27_215_; lean_object* v___x_216_; lean_object* v_buckets_x27_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v_size_x27_215_ = lean_nat_add(v_size_193_, v___x_214_);
lean_dec(v_size_193_);
lean_inc(v_bkt_209_);
v___x_216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_216_, 0, v_a_191_);
lean_ctor_set(v___x_216_, 1, v_b_192_);
lean_ctor_set(v___x_216_, 2, v_bkt_209_);
v_buckets_x27_217_ = lean_array_uset(v_buckets_194_, v___x_208_, v___x_216_);
v___x_218_ = lean_unsigned_to_nat(4u);
v___x_219_ = lean_nat_mul(v_size_x27_215_, v___x_218_);
v___x_220_ = lean_unsigned_to_nat(3u);
v___x_221_ = lean_nat_div(v___x_219_, v___x_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_array_get_size(v_buckets_x27_217_);
v___x_223_ = lean_nat_dec_le(v___x_221_, v___x_222_);
lean_dec(v___x_221_);
if (v___x_223_ == 0)
{
lean_object* v_val_224_; lean_object* v___x_226_; 
v_val_224_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_buckets_x27_217_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v_val_224_);
lean_ctor_set(v___x_212_, 0, v_size_x27_215_);
v___x_226_ = v___x_212_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_size_x27_215_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_val_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
else
{
lean_object* v___x_229_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v_buckets_x27_217_);
lean_ctor_set(v___x_212_, 0, v_size_x27_215_);
v___x_229_ = v___x_212_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_size_x27_215_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_buckets_x27_217_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
else
{
lean_dec(v_b_192_);
lean_dec_ref(v_a_191_);
return v_m_190_;
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_box(0);
v___x_238_ = lean_unsigned_to_nat(16u);
v___x_239_ = lean_mk_array(v___x_238_, v___x_237_);
return v___x_239_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_240_);
return v___x_242_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4(void){
_start:
{
lean_object* v___x_243_; lean_object* v_sats_244_; lean_object* v___x_245_; 
v___x_243_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3);
v_sats_244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1));
v___x_245_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_245_, 0, v_sats_244_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set(v___x_245_, 2, v___x_243_);
lean_ctor_set(v___x_245_, 3, v___x_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(lean_object* v_as_246_, size_t v_sz_247_, size_t v_i_248_, lean_object* v_b_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_a_260_; uint8_t v___x_264_; 
v___x_264_ = lean_usize_dec_lt(v_i_248_, v_sz_247_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v_b_249_);
return v___x_265_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0));
v___x_267_ = l_Lean_Core_checkSystem(v___x_266_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec_ref_known(v___x_267_, 1);
v_a_268_ = lean_array_uget_borrowed(v_as_246_, v_i_248_);
lean_inc(v_a_268_);
v___x_269_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed), 11, 1);
lean_closure_set(v___x_269_, 0, v_a_268_);
v___x_270_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4);
v___x_271_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v___x_269_, v___x_270_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v_fst_273_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
v_fst_273_ = lean_ctor_get(v_a_272_, 0);
lean_inc(v_fst_273_);
if (lean_obj_tag(v_fst_273_) == 1)
{
lean_object* v_snd_274_; lean_object* v_fst_275_; lean_object* v_snd_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_286_; 
v_snd_274_ = lean_ctor_get(v_a_272_, 1);
lean_inc(v_snd_274_);
lean_dec(v_a_272_);
v_fst_275_ = lean_ctor_get(v_b_249_, 0);
v_snd_276_ = lean_ctor_get(v_b_249_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v_b_249_);
if (v_isSharedCheck_286_ == 0)
{
v___x_278_ = v_b_249_;
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_snd_276_);
lean_inc(v_fst_275_);
lean_dec(v_b_249_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v_val_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v_val_280_ = lean_ctor_get(v_fst_273_, 0);
lean_inc(v_val_280_);
lean_dec_ref_known(v_fst_273_, 1);
v___x_281_ = l_Array_append___redArg(v_fst_275_, v_snd_274_);
lean_dec(v_snd_274_);
v___x_282_ = lean_array_push(v___x_281_, v_val_280_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_282_);
v___x_284_ = v___x_278_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_snd_276_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
v_a_260_ = v___x_284_;
goto v___jp_259_;
}
}
}
else
{
lean_object* v_fst_287_; lean_object* v_snd_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_297_; 
lean_dec(v_fst_273_);
lean_dec(v_a_272_);
v_fst_287_ = lean_ctor_get(v_b_249_, 0);
v_snd_288_ = lean_ctor_get(v_b_249_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v_b_249_);
if (v_isSharedCheck_297_ == 0)
{
v___x_290_ = v_b_249_;
v_isShared_291_ = v_isSharedCheck_297_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_snd_288_);
lean_inc(v_fst_287_);
lean_dec(v_b_249_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_297_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_292_ = lean_box(0);
lean_inc(v_a_268_);
v___x_293_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_snd_288_, v_a_268_, v___x_292_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 1, v___x_293_);
v___x_295_ = v___x_290_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_fst_287_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
v_a_260_ = v___x_295_;
goto v___jp_259_;
}
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref(v_b_249_);
v_a_298_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_271_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_271_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec_ref(v_b_249_);
v_a_306_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_267_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_267_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
v___jp_259_:
{
size_t v___x_261_; size_t v___x_262_; 
v___x_261_ = ((size_t)1ULL);
v___x_262_ = lean_usize_add(v_i_248_, v___x_261_);
v_i_248_ = v___x_262_;
v_b_249_ = v_a_260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___boxed(lean_object* v_as_314_, lean_object* v_sz_315_, lean_object* v_i_316_, lean_object* v_b_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
size_t v_sz_boxed_327_; size_t v_i_boxed_328_; lean_object* v_res_329_; 
v_sz_boxed_327_ = lean_unbox_usize(v_sz_315_);
lean_dec(v_sz_315_);
v_i_boxed_328_ = lean_unbox_usize(v_i_316_);
lean_dec(v_i_316_);
v_res_329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v_as_314_, v_sz_boxed_327_, v_i_boxed_328_, v_b_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec_ref(v_as_314_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(lean_object* v_a_330_, lean_object* v_b_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_array_339_; lean_object* v_start_340_; lean_object* v_stop_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_356_; 
v_array_339_ = lean_ctor_get(v_a_330_, 0);
v_start_340_ = lean_ctor_get(v_a_330_, 1);
v_stop_341_ = lean_ctor_get(v_a_330_, 2);
v_isSharedCheck_356_ = !lean_is_exclusive(v_a_330_);
if (v_isSharedCheck_356_ == 0)
{
v___x_343_ = v_a_330_;
v_isShared_344_ = v_isSharedCheck_356_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_stop_341_);
lean_inc(v_start_340_);
lean_inc(v_array_339_);
lean_dec(v_a_330_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_356_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
uint8_t v___x_345_; 
v___x_345_ = lean_nat_dec_lt(v_start_340_, v_stop_341_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
lean_del_object(v___x_343_);
lean_dec(v_stop_341_);
lean_dec(v_start_340_);
lean_dec_ref(v_array_339_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v_b_331_);
return v___x_346_;
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_array_fget_borrowed(v_array_339_, v_start_340_);
lean_inc(v___x_347_);
v___x_348_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_b_331_, v___x_347_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 1);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_add(v_start_340_, v___x_350_);
lean_dec(v_start_340_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v___x_351_);
v___x_353_ = v___x_343_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_array_339_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_stop_341_);
v___x_353_ = v_reuseFailAlloc_355_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
v_a_330_ = v___x_353_;
v_b_331_ = v_a_349_;
goto _start;
}
}
else
{
lean_del_object(v___x_343_);
lean_dec(v_stop_341_);
lean_dec(v_start_340_);
lean_dec_ref(v_array_339_);
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg___boxed(lean_object* v_a_357_, lean_object* v_b_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_357_, v_b_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_366_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1));
v___x_371_ = l_Lean_MessageData_ofFormat(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(lean_object* v_sats_372_, lean_object* v_unusedHypotheses_373_, lean_object* v___x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; size_t v_sz_385_; size_t v___x_386_; lean_object* v___x_387_; 
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_sats_372_);
lean_ctor_set(v___x_384_, 1, v_unusedHypotheses_373_);
v_sz_385_ = lean_array_size(v___y_375_);
v___x_386_ = ((size_t)0ULL);
v___x_387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v___y_375_, v_sz_385_, v___x_386_, v___x_384_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_387_, 1);
v_fst_389_ = lean_ctor_get(v_a_388_, 0);
lean_inc(v_fst_389_);
v_snd_390_ = lean_ctor_get(v_a_388_, 1);
lean_inc(v_snd_390_);
lean_dec(v_a_388_);
v___x_391_ = lean_array_get_size(v_fst_389_);
v___x_392_ = lean_nat_dec_eq(v___x_391_, v___x_374_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_393_ = lean_array_fget(v_fst_389_, v___x_374_);
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = l_Array_toSubarray___redArg(v_fst_389_, v___x_394_, v___x_391_);
v___x_396_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v___x_395_, v___x_393_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_409_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_409_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_409_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_409_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_bvExpr_401_; lean_object* v_expr_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v_bvExpr_401_ = lean_ctor_get(v_a_397_, 0);
v_expr_402_ = lean_ctor_get(v_a_397_, 2);
lean_inc_ref(v_expr_402_);
lean_inc_ref(v_bvExpr_401_);
v___x_403_ = l_Lean_ShareCommon_shareCommon___redArg(v_bvExpr_401_);
v___x_404_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed), 11, 1);
lean_closure_set(v___x_404_, 0, v_a_397_);
v___x_405_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
lean_ctor_set(v___x_405_, 2, v_snd_390_);
lean_ctor_set(v___x_405_, 3, v_expr_402_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_405_);
v___x_407_ = v___x_399_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_snd_390_);
v_a_410_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_396_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_396_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v_snd_390_);
lean_dec(v_fst_389_);
v___x_418_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2);
v___x_419_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v___x_418_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
return v___x_419_;
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
v_a_420_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_387_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_387_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed(lean_object* v_sats_428_, lean_object* v_unusedHypotheses_429_, lean_object* v___x_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(v_sats_428_, v_unusedHypotheses_429_, v___x_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___x_430_);
return v_res_440_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_box(0);
v___x_442_ = lean_unsigned_to_nat(16u);
v___x_443_ = lean_mk_array(v___x_442_, v___x_441_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_unusedHypotheses_446_; 
v___x_444_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0);
v___x_445_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_unusedHypotheses_446_, 0, v___x_445_);
lean_ctor_set(v_unusedHypotheses_446_, 1, v___x_444_);
return v_unusedHypotheses_446_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2(void){
_start:
{
lean_object* v___x_447_; lean_object* v_unusedHypotheses_448_; lean_object* v_sats_449_; lean_object* v___f_450_; 
v___x_447_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_448_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1);
v_sats_449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1));
v___f_450_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed), 12, 3);
lean_closure_set(v___f_450_, 0, v_sats_449_);
lean_closure_set(v___f_450_, 1, v_unusedHypotheses_448_);
lean_closure_set(v___f_450_, 2, v___x_447_);
return v___f_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV(lean_object* v_g_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___f_461_; lean_object* v___x_462_; 
v___f_461_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2);
v___x_462_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_g_451_, v___f_461_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___boxed(lean_object* v_g_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0(lean_object* v_00_u03b2_474_, lean_object* v_m_475_, lean_object* v_a_476_, lean_object* v_b_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_m_475_, v_a_476_, v_b_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(lean_object* v_inst_479_, lean_object* v_R_480_, lean_object* v_a_481_, lean_object* v_b_482_, lean_object* v_c_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_481_, v_b_482_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___boxed(lean_object* v_inst_494_, lean_object* v_R_495_, lean_object* v_a_496_, lean_object* v_b_497_, lean_object* v_c_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(v_inst_494_, v_R_495_, v_a_496_, v_b_497_, v_c_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(lean_object* v_00_u03b1_509_, lean_object* v_msg_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_510_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___boxed(lean_object* v_00_u03b1_521_, lean_object* v_msg_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(v_00_u03b1_521_, v_msg_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_532_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(lean_object* v_00_u03b2_533_, lean_object* v_a_534_, lean_object* v_x_535_){
_start:
{
uint8_t v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_534_, v_x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___boxed(lean_object* v_00_u03b2_537_, lean_object* v_a_538_, lean_object* v_x_539_){
_start:
{
uint8_t v_res_540_; lean_object* v_r_541_; 
v_res_540_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(v_00_u03b2_537_, v_a_538_, v_x_539_);
lean_dec(v_x_539_);
lean_dec_ref(v_a_538_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1(lean_object* v_00_u03b2_542_, lean_object* v_data_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_data_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_545_, lean_object* v_i_546_, lean_object* v_source_547_, lean_object* v_target_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v_i_546_, v_source_547_, v_target_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_550_, lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(v_x_551_, v_x_552_);
return v___x_553_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_unsigned_to_nat(32u);
v___x_555_ = lean_mk_empty_array_with_capacity(v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1(void){
_start:
{
size_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_557_ = ((size_t)5ULL);
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_unsigned_to_nat(32u);
v___x_560_ = lean_mk_empty_array_with_capacity(v___x_559_);
v___x_561_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0);
v___x_562_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_560_);
lean_ctor_set(v___x_562_, 2, v___x_558_);
lean_ctor_set(v___x_562_, 3, v___x_558_);
lean_ctor_set_usize(v___x_562_, 4, v___x_557_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; lean_object* v_traceState_566_; lean_object* v_traces_567_; lean_object* v___x_568_; lean_object* v_traceState_569_; lean_object* v_env_570_; lean_object* v_nextMacroScope_571_; lean_object* v_ngen_572_; lean_object* v_auxDeclNGen_573_; lean_object* v_cache_574_; lean_object* v_messages_575_; lean_object* v_infoState_576_; lean_object* v_snapshotTasks_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_596_; 
v___x_565_ = lean_st_ref_get(v___y_563_);
v_traceState_566_ = lean_ctor_get(v___x_565_, 4);
lean_inc_ref(v_traceState_566_);
lean_dec(v___x_565_);
v_traces_567_ = lean_ctor_get(v_traceState_566_, 0);
lean_inc_ref(v_traces_567_);
lean_dec_ref(v_traceState_566_);
v___x_568_ = lean_st_ref_take(v___y_563_);
v_traceState_569_ = lean_ctor_get(v___x_568_, 4);
v_env_570_ = lean_ctor_get(v___x_568_, 0);
v_nextMacroScope_571_ = lean_ctor_get(v___x_568_, 1);
v_ngen_572_ = lean_ctor_get(v___x_568_, 2);
v_auxDeclNGen_573_ = lean_ctor_get(v___x_568_, 3);
v_cache_574_ = lean_ctor_get(v___x_568_, 5);
v_messages_575_ = lean_ctor_get(v___x_568_, 6);
v_infoState_576_ = lean_ctor_get(v___x_568_, 7);
v_snapshotTasks_577_ = lean_ctor_get(v___x_568_, 8);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_596_ == 0)
{
v___x_579_ = v___x_568_;
v_isShared_580_ = v_isSharedCheck_596_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snapshotTasks_577_);
lean_inc(v_infoState_576_);
lean_inc(v_messages_575_);
lean_inc(v_cache_574_);
lean_inc(v_traceState_569_);
lean_inc(v_auxDeclNGen_573_);
lean_inc(v_ngen_572_);
lean_inc(v_nextMacroScope_571_);
lean_inc(v_env_570_);
lean_dec(v___x_568_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_596_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
uint64_t v_tid_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_594_; 
v_tid_581_ = lean_ctor_get_uint64(v_traceState_569_, sizeof(void*)*1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_traceState_569_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v_traceState_569_, 0);
lean_dec(v_unused_595_);
v___x_583_ = v_traceState_569_;
v_isShared_584_ = v_isSharedCheck_594_;
goto v_resetjp_582_;
}
else
{
lean_dec(v_traceState_569_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_594_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_585_);
v___x_587_ = v___x_583_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_585_);
lean_ctor_set_uint64(v_reuseFailAlloc_593_, sizeof(void*)*1, v_tid_581_);
v___x_587_ = v_reuseFailAlloc_593_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_589_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 4, v___x_587_);
v___x_589_ = v___x_579_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_env_570_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_nextMacroScope_571_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v_ngen_572_);
lean_ctor_set(v_reuseFailAlloc_592_, 3, v_auxDeclNGen_573_);
lean_ctor_set(v_reuseFailAlloc_592_, 4, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_592_, 5, v_cache_574_);
lean_ctor_set(v_reuseFailAlloc_592_, 6, v_messages_575_);
lean_ctor_set(v_reuseFailAlloc_592_, 7, v_infoState_576_);
lean_ctor_set(v_reuseFailAlloc_592_, 8, v_snapshotTasks_577_);
v___x_589_ = v_reuseFailAlloc_592_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_st_ref_put(v___y_563_, v___x_589_);
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v_traces_567_);
return v___x_591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___boxed(lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(v___y_597_);
lean_dec(v___y_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(v___y_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___boxed(lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_619_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(lean_object* v_opts_620_, lean_object* v_opt_621_){
_start:
{
lean_object* v_name_622_; lean_object* v_defValue_623_; lean_object* v_map_624_; lean_object* v___x_625_; 
v_name_622_ = lean_ctor_get(v_opt_621_, 0);
v_defValue_623_ = lean_ctor_get(v_opt_621_, 1);
v_map_624_ = lean_ctor_get(v_opts_620_, 0);
v___x_625_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_624_, v_name_622_);
if (lean_obj_tag(v___x_625_) == 0)
{
uint8_t v___x_626_; 
v___x_626_ = lean_unbox(v_defValue_623_);
return v___x_626_;
}
else
{
lean_object* v_val_627_; 
v_val_627_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_val_627_);
lean_dec_ref_known(v___x_625_, 1);
if (lean_obj_tag(v_val_627_) == 1)
{
uint8_t v_v_628_; 
v_v_628_ = lean_ctor_get_uint8(v_val_627_, 0);
lean_dec_ref_known(v_val_627_, 0);
return v_v_628_;
}
else
{
uint8_t v___x_629_; 
lean_dec(v_val_627_);
v___x_629_ = lean_unbox(v_defValue_623_);
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___boxed(lean_object* v_opts_630_, lean_object* v_opt_631_){
_start:
{
uint8_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_opts_630_, v_opt_631_);
lean_dec_ref(v_opt_631_);
lean_dec_ref(v_opts_630_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1));
v___x_638_ = l_Lean_MessageData_ofFormat(v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(lean_object* v_x_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed(lean_object* v_x_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(v_x_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec_ref(v_x_651_);
return v_res_661_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14(lean_object* v_e_662_){
_start:
{
if (lean_obj_tag(v_e_662_) == 0)
{
uint8_t v___x_663_; 
v___x_663_ = 2;
return v___x_663_;
}
else
{
uint8_t v___x_664_; 
v___x_664_ = 0;
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14___boxed(lean_object* v_e_665_){
_start:
{
uint8_t v_res_666_; lean_object* v_r_667_; 
v_res_666_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14(v_e_665_);
lean_dec_ref(v_e_665_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(lean_object* v_opts_668_, lean_object* v_opt_669_){
_start:
{
lean_object* v_name_670_; lean_object* v_defValue_671_; lean_object* v_map_672_; lean_object* v___x_673_; 
v_name_670_ = lean_ctor_get(v_opt_669_, 0);
v_defValue_671_ = lean_ctor_get(v_opt_669_, 1);
v_map_672_ = lean_ctor_get(v_opts_668_, 0);
v___x_673_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_672_, v_name_670_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_inc(v_defValue_671_);
return v_defValue_671_;
}
else
{
lean_object* v_val_674_; 
v_val_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v___x_673_, 1);
if (lean_obj_tag(v_val_674_) == 3)
{
lean_object* v_v_675_; 
v_v_675_ = lean_ctor_get(v_val_674_, 0);
lean_inc(v_v_675_);
lean_dec_ref_known(v_val_674_, 1);
return v_v_675_;
}
else
{
lean_dec(v_val_674_);
lean_inc(v_defValue_671_);
return v_defValue_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15___boxed(lean_object* v_opts_676_, lean_object* v_opt_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(v_opts_676_, v_opt_677_);
lean_dec_ref(v_opt_677_);
lean_dec_ref(v_opts_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17(size_t v_sz_679_, size_t v_i_680_, lean_object* v_bs_681_){
_start:
{
uint8_t v___x_682_; 
v___x_682_ = lean_usize_dec_lt(v_i_680_, v_sz_679_);
if (v___x_682_ == 0)
{
return v_bs_681_;
}
else
{
lean_object* v_v_683_; lean_object* v_msg_684_; lean_object* v___x_685_; lean_object* v_bs_x27_686_; size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
v_v_683_ = lean_array_uget_borrowed(v_bs_681_, v_i_680_);
v_msg_684_ = lean_ctor_get(v_v_683_, 1);
lean_inc_ref(v_msg_684_);
v___x_685_ = lean_unsigned_to_nat(0u);
v_bs_x27_686_ = lean_array_uset(v_bs_681_, v_i_680_, v___x_685_);
v___x_687_ = ((size_t)1ULL);
v___x_688_ = lean_usize_add(v_i_680_, v___x_687_);
v___x_689_ = lean_array_uset(v_bs_x27_686_, v_i_680_, v_msg_684_);
v_i_680_ = v___x_688_;
v_bs_681_ = v___x_689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17___boxed(lean_object* v_sz_691_, lean_object* v_i_692_, lean_object* v_bs_693_){
_start:
{
size_t v_sz_boxed_694_; size_t v_i_boxed_695_; lean_object* v_res_696_; 
v_sz_boxed_694_ = lean_unbox_usize(v_sz_691_);
lean_dec(v_sz_691_);
v_i_boxed_695_ = lean_unbox_usize(v_i_692_);
lean_dec(v_i_692_);
v_res_696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17(v_sz_boxed_694_, v_i_boxed_695_, v_bs_693_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg(lean_object* v_oldTraces_697_, lean_object* v_data_698_, lean_object* v_ref_699_, lean_object* v_msg_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_toCold_706_; lean_object* v_options_707_; lean_object* v_currRecDepth_708_; lean_object* v_maxRecDepth_709_; lean_object* v_ref_710_; lean_object* v_currNamespace_711_; lean_object* v_openDecls_712_; lean_object* v_initHeartbeats_713_; lean_object* v_maxHeartbeats_714_; lean_object* v_currMacroScope_715_; uint8_t v_diag_716_; uint8_t v_suppressElabErrors_717_; lean_object* v___x_718_; lean_object* v_traceState_719_; lean_object* v_traces_720_; lean_object* v_ref_721_; lean_object* v___x_722_; lean_object* v___x_723_; size_t v_sz_724_; size_t v___x_725_; lean_object* v___x_726_; lean_object* v_msg_727_; lean_object* v___x_728_; lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_766_; 
v_toCold_706_ = lean_ctor_get(v___y_703_, 0);
v_options_707_ = lean_ctor_get(v___y_703_, 1);
v_currRecDepth_708_ = lean_ctor_get(v___y_703_, 2);
v_maxRecDepth_709_ = lean_ctor_get(v___y_703_, 3);
v_ref_710_ = lean_ctor_get(v___y_703_, 4);
v_currNamespace_711_ = lean_ctor_get(v___y_703_, 5);
v_openDecls_712_ = lean_ctor_get(v___y_703_, 6);
v_initHeartbeats_713_ = lean_ctor_get(v___y_703_, 7);
v_maxHeartbeats_714_ = lean_ctor_get(v___y_703_, 8);
v_currMacroScope_715_ = lean_ctor_get(v___y_703_, 9);
v_diag_716_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*10);
v_suppressElabErrors_717_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*10 + 1);
v___x_718_ = lean_st_ref_get(v___y_704_);
v_traceState_719_ = lean_ctor_get(v___x_718_, 4);
lean_inc_ref(v_traceState_719_);
lean_dec(v___x_718_);
v_traces_720_ = lean_ctor_get(v_traceState_719_, 0);
lean_inc_ref(v_traces_720_);
lean_dec_ref(v_traceState_719_);
v_ref_721_ = l_Lean_replaceRef(v_ref_699_, v_ref_710_);
lean_inc(v_currMacroScope_715_);
lean_inc(v_maxHeartbeats_714_);
lean_inc(v_initHeartbeats_713_);
lean_inc(v_openDecls_712_);
lean_inc(v_currNamespace_711_);
lean_inc(v_maxRecDepth_709_);
lean_inc(v_currRecDepth_708_);
lean_inc_ref(v_options_707_);
lean_inc_ref(v_toCold_706_);
v___x_722_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_722_, 0, v_toCold_706_);
lean_ctor_set(v___x_722_, 1, v_options_707_);
lean_ctor_set(v___x_722_, 2, v_currRecDepth_708_);
lean_ctor_set(v___x_722_, 3, v_maxRecDepth_709_);
lean_ctor_set(v___x_722_, 4, v_ref_721_);
lean_ctor_set(v___x_722_, 5, v_currNamespace_711_);
lean_ctor_set(v___x_722_, 6, v_openDecls_712_);
lean_ctor_set(v___x_722_, 7, v_initHeartbeats_713_);
lean_ctor_set(v___x_722_, 8, v_maxHeartbeats_714_);
lean_ctor_set(v___x_722_, 9, v_currMacroScope_715_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*10, v_diag_716_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*10 + 1, v_suppressElabErrors_717_);
v___x_723_ = l_Lean_PersistentArray_toArray___redArg(v_traces_720_);
lean_dec_ref(v_traces_720_);
v_sz_724_ = lean_array_size(v___x_723_);
v___x_725_ = ((size_t)0ULL);
v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17(v_sz_724_, v___x_725_, v___x_723_);
v_msg_727_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_727_, 0, v_data_698_);
lean_ctor_set(v_msg_727_, 1, v_msg_700_);
lean_ctor_set(v_msg_727_, 2, v___x_726_);
v___x_728_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_727_, v___y_701_, v___y_702_, v___x_722_, v___y_704_);
lean_dec_ref_known(v___x_722_, 10);
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_766_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_766_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_766_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v_traceState_734_; lean_object* v_env_735_; lean_object* v_nextMacroScope_736_; lean_object* v_ngen_737_; lean_object* v_auxDeclNGen_738_; lean_object* v_cache_739_; lean_object* v_messages_740_; lean_object* v_infoState_741_; lean_object* v_snapshotTasks_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_765_; 
v___x_733_ = lean_st_ref_take(v___y_704_);
v_traceState_734_ = lean_ctor_get(v___x_733_, 4);
v_env_735_ = lean_ctor_get(v___x_733_, 0);
v_nextMacroScope_736_ = lean_ctor_get(v___x_733_, 1);
v_ngen_737_ = lean_ctor_get(v___x_733_, 2);
v_auxDeclNGen_738_ = lean_ctor_get(v___x_733_, 3);
v_cache_739_ = lean_ctor_get(v___x_733_, 5);
v_messages_740_ = lean_ctor_get(v___x_733_, 6);
v_infoState_741_ = lean_ctor_get(v___x_733_, 7);
v_snapshotTasks_742_ = lean_ctor_get(v___x_733_, 8);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_765_ == 0)
{
v___x_744_ = v___x_733_;
v_isShared_745_ = v_isSharedCheck_765_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_snapshotTasks_742_);
lean_inc(v_infoState_741_);
lean_inc(v_messages_740_);
lean_inc(v_cache_739_);
lean_inc(v_traceState_734_);
lean_inc(v_auxDeclNGen_738_);
lean_inc(v_ngen_737_);
lean_inc(v_nextMacroScope_736_);
lean_inc(v_env_735_);
lean_dec(v___x_733_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_765_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
uint64_t v_tid_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_763_; 
v_tid_746_ = lean_ctor_get_uint64(v_traceState_734_, sizeof(void*)*1);
v_isSharedCheck_763_ = !lean_is_exclusive(v_traceState_734_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v_traceState_734_, 0);
lean_dec(v_unused_764_);
v___x_748_ = v_traceState_734_;
v_isShared_749_ = v_isSharedCheck_763_;
goto v_resetjp_747_;
}
else
{
lean_dec(v_traceState_734_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_763_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v_ref_699_);
lean_ctor_set(v___x_750_, 1, v_a_729_);
v___x_751_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_697_, v___x_750_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_751_);
v___x_753_ = v___x_748_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_751_);
lean_ctor_set_uint64(v_reuseFailAlloc_762_, sizeof(void*)*1, v_tid_746_);
v___x_753_ = v_reuseFailAlloc_762_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 4, v___x_753_);
v___x_755_ = v___x_744_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_env_735_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_nextMacroScope_736_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_ngen_737_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_auxDeclNGen_738_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_761_, 5, v_cache_739_);
lean_ctor_set(v_reuseFailAlloc_761_, 6, v_messages_740_);
lean_ctor_set(v_reuseFailAlloc_761_, 7, v_infoState_741_);
lean_ctor_set(v_reuseFailAlloc_761_, 8, v_snapshotTasks_742_);
v___x_755_ = v_reuseFailAlloc_761_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_756_ = lean_st_ref_put(v___y_704_, v___x_755_);
v___x_757_ = lean_box(0);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_757_);
v___x_759_ = v___x_731_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg___boxed(lean_object* v_oldTraces_767_, lean_object* v_data_768_, lean_object* v_ref_769_, lean_object* v_msg_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg(v_oldTraces_767_, v_data_768_, v_ref_769_, v_msg_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(lean_object* v_x_777_){
_start:
{
if (lean_obj_tag(v_x_777_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
v_a_779_ = lean_ctor_get(v_x_777_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v_x_777_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v_x_777_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 1);
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v_a_787_ = lean_ctor_get(v_x_777_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v_x_777_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v_x_777_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v_x_777_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set_tag(v___x_789_, 0);
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg___boxed(lean_object* v_x_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_x_795_);
return v_res_797_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0(void){
_start:
{
lean_object* v___x_798_; double v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_float_of_nat(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__1));
v___x_802_ = l_Lean_stringToMessageData(v___x_801_);
return v___x_802_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3(void){
_start:
{
lean_object* v___x_803_; double v___x_804_; 
v___x_803_ = lean_unsigned_to_nat(1000u);
v___x_804_ = lean_float_of_nat(v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(lean_object* v_cls_805_, uint8_t v_collapsed_806_, lean_object* v_tag_807_, lean_object* v_opts_808_, uint8_t v_clsEnabled_809_, lean_object* v_oldTraces_810_, lean_object* v_msg_811_, lean_object* v_resStartStop_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_fst_822_; lean_object* v_snd_823_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v_data_827_; lean_object* v_fst_838_; lean_object* v_snd_839_; lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v___y_843_; lean_object* v_a_844_; uint8_t v___y_859_; double v___y_890_; 
v_fst_822_ = lean_ctor_get(v_resStartStop_812_, 0);
lean_inc(v_fst_822_);
v_snd_823_ = lean_ctor_get(v_resStartStop_812_, 1);
lean_inc(v_snd_823_);
lean_dec_ref(v_resStartStop_812_);
v_fst_838_ = lean_ctor_get(v_snd_823_, 0);
lean_inc(v_fst_838_);
v_snd_839_ = lean_ctor_get(v_snd_823_, 1);
lean_inc(v_snd_839_);
lean_dec(v_snd_823_);
v___x_840_ = l_Lean_trace_profiler;
v___x_841_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_opts_808_, v___x_840_);
if (v___x_841_ == 0)
{
v___y_859_ = v___x_841_;
goto v___jp_858_;
}
else
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = l_Lean_trace_profiler_useHeartbeats;
v___x_896_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_opts_808_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; double v___x_899_; double v___x_900_; double v___x_901_; 
v___x_897_ = l_Lean_trace_profiler_threshold;
v___x_898_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(v_opts_808_, v___x_897_);
v___x_899_ = lean_float_of_nat(v___x_898_);
v___x_900_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3);
v___x_901_ = lean_float_div(v___x_899_, v___x_900_);
v___y_890_ = v___x_901_;
goto v___jp_889_;
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; double v___x_904_; 
v___x_902_ = l_Lean_trace_profiler_threshold;
v___x_903_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(v_opts_808_, v___x_902_);
v___x_904_ = lean_float_of_nat(v___x_903_);
v___y_890_ = v___x_904_;
goto v___jp_889_;
}
}
v___jp_824_:
{
lean_object* v___x_828_; 
lean_inc(v___y_826_);
v___x_828_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg(v_oldTraces_810_, v_data_827_, v___y_826_, v___y_825_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_829_; 
lean_dec_ref_known(v___x_828_, 1);
v___x_829_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_fst_822_);
return v___x_829_;
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec(v_fst_822_);
v_a_830_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_828_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_828_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
v___jp_842_:
{
uint8_t v_result_845_; lean_object* v___x_846_; lean_object* v___x_847_; double v___x_848_; lean_object* v_data_849_; 
v_result_845_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14(v_fst_822_);
v___x_846_ = lean_box(v_result_845_);
v___x_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
v___x_848_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0);
lean_inc_ref(v_tag_807_);
lean_inc_ref(v___x_847_);
lean_inc(v_cls_805_);
v_data_849_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_849_, 0, v_cls_805_);
lean_ctor_set(v_data_849_, 1, v___x_847_);
lean_ctor_set(v_data_849_, 2, v_tag_807_);
lean_ctor_set_float(v_data_849_, sizeof(void*)*3, v___x_848_);
lean_ctor_set_float(v_data_849_, sizeof(void*)*3 + 8, v___x_848_);
lean_ctor_set_uint8(v_data_849_, sizeof(void*)*3 + 16, v_collapsed_806_);
if (v___x_841_ == 0)
{
lean_dec_ref_known(v___x_847_, 1);
lean_dec(v_snd_839_);
lean_dec(v_fst_838_);
lean_dec_ref(v_tag_807_);
lean_dec(v_cls_805_);
v___y_825_ = v_a_844_;
v___y_826_ = v___y_843_;
v_data_827_ = v_data_849_;
goto v___jp_824_;
}
else
{
lean_object* v_data_850_; double v___x_851_; double v___x_852_; 
lean_dec_ref_known(v_data_849_, 3);
v_data_850_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_850_, 0, v_cls_805_);
lean_ctor_set(v_data_850_, 1, v___x_847_);
lean_ctor_set(v_data_850_, 2, v_tag_807_);
v___x_851_ = lean_unbox_float(v_fst_838_);
lean_dec(v_fst_838_);
lean_ctor_set_float(v_data_850_, sizeof(void*)*3, v___x_851_);
v___x_852_ = lean_unbox_float(v_snd_839_);
lean_dec(v_snd_839_);
lean_ctor_set_float(v_data_850_, sizeof(void*)*3 + 8, v___x_852_);
lean_ctor_set_uint8(v_data_850_, sizeof(void*)*3 + 16, v_collapsed_806_);
v___y_825_ = v_a_844_;
v___y_826_ = v___y_843_;
v_data_827_ = v_data_850_;
goto v___jp_824_;
}
}
v___jp_853_:
{
lean_object* v_ref_854_; lean_object* v___x_855_; 
v_ref_854_ = lean_ctor_get(v___y_819_, 4);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v_fst_822_);
v___x_855_ = lean_apply_10(v_msg_811_, v_fst_822_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, lean_box(0));
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v___y_843_ = v_ref_854_;
v_a_844_ = v_a_856_;
goto v___jp_842_;
}
else
{
lean_object* v___x_857_; 
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2);
v___y_843_ = v_ref_854_;
v_a_844_ = v___x_857_;
goto v___jp_842_;
}
}
v___jp_858_:
{
if (v_clsEnabled_809_ == 0)
{
if (v___y_859_ == 0)
{
lean_object* v___x_860_; lean_object* v_traceState_861_; lean_object* v_env_862_; lean_object* v_nextMacroScope_863_; lean_object* v_ngen_864_; lean_object* v_auxDeclNGen_865_; lean_object* v_cache_866_; lean_object* v_messages_867_; lean_object* v_infoState_868_; lean_object* v_snapshotTasks_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_snd_839_);
lean_dec(v_fst_838_);
lean_dec_ref(v_msg_811_);
lean_dec_ref(v_tag_807_);
lean_dec(v_cls_805_);
v___x_860_ = lean_st_ref_take(v___y_820_);
v_traceState_861_ = lean_ctor_get(v___x_860_, 4);
v_env_862_ = lean_ctor_get(v___x_860_, 0);
v_nextMacroScope_863_ = lean_ctor_get(v___x_860_, 1);
v_ngen_864_ = lean_ctor_get(v___x_860_, 2);
v_auxDeclNGen_865_ = lean_ctor_get(v___x_860_, 3);
v_cache_866_ = lean_ctor_get(v___x_860_, 5);
v_messages_867_ = lean_ctor_get(v___x_860_, 6);
v_infoState_868_ = lean_ctor_get(v___x_860_, 7);
v_snapshotTasks_869_ = lean_ctor_get(v___x_860_, 8);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_888_ == 0)
{
v___x_871_ = v___x_860_;
v_isShared_872_ = v_isSharedCheck_888_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_snapshotTasks_869_);
lean_inc(v_infoState_868_);
lean_inc(v_messages_867_);
lean_inc(v_cache_866_);
lean_inc(v_traceState_861_);
lean_inc(v_auxDeclNGen_865_);
lean_inc(v_ngen_864_);
lean_inc(v_nextMacroScope_863_);
lean_inc(v_env_862_);
lean_dec(v___x_860_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_888_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
uint64_t v_tid_873_; lean_object* v_traces_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_887_; 
v_tid_873_ = lean_ctor_get_uint64(v_traceState_861_, sizeof(void*)*1);
v_traces_874_ = lean_ctor_get(v_traceState_861_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v_traceState_861_);
if (v_isSharedCheck_887_ == 0)
{
v___x_876_ = v_traceState_861_;
v_isShared_877_ = v_isSharedCheck_887_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_traces_874_);
lean_dec(v_traceState_861_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_887_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_810_, v_traces_874_);
lean_dec_ref(v_traces_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_878_);
v___x_880_ = v___x_876_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_878_);
lean_ctor_set_uint64(v_reuseFailAlloc_886_, sizeof(void*)*1, v_tid_873_);
v___x_880_ = v_reuseFailAlloc_886_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_882_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 4, v___x_880_);
v___x_882_ = v___x_871_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_env_862_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_nextMacroScope_863_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_ngen_864_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v_auxDeclNGen_865_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_885_, 5, v_cache_866_);
lean_ctor_set(v_reuseFailAlloc_885_, 6, v_messages_867_);
lean_ctor_set(v_reuseFailAlloc_885_, 7, v_infoState_868_);
lean_ctor_set(v_reuseFailAlloc_885_, 8, v_snapshotTasks_869_);
v___x_882_ = v_reuseFailAlloc_885_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_st_ref_put(v___y_820_, v___x_882_);
v___x_884_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_fst_822_);
return v___x_884_;
}
}
}
}
}
else
{
goto v___jp_853_;
}
}
else
{
goto v___jp_853_;
}
}
v___jp_889_:
{
double v___x_891_; double v___x_892_; double v___x_893_; uint8_t v___x_894_; 
v___x_891_ = lean_unbox_float(v_snd_839_);
v___x_892_ = lean_unbox_float(v_fst_838_);
v___x_893_ = lean_float_sub(v___x_891_, v___x_892_);
v___x_894_ = lean_float_decLt(v___y_890_, v___x_893_);
v___y_859_ = v___x_894_;
goto v___jp_858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___boxed(lean_object** _args){
lean_object* v_cls_905_ = _args[0];
lean_object* v_collapsed_906_ = _args[1];
lean_object* v_tag_907_ = _args[2];
lean_object* v_opts_908_ = _args[3];
lean_object* v_clsEnabled_909_ = _args[4];
lean_object* v_oldTraces_910_ = _args[5];
lean_object* v_msg_911_ = _args[6];
lean_object* v_resStartStop_912_ = _args[7];
lean_object* v___y_913_ = _args[8];
lean_object* v___y_914_ = _args[9];
lean_object* v___y_915_ = _args[10];
lean_object* v___y_916_ = _args[11];
lean_object* v___y_917_ = _args[12];
lean_object* v___y_918_ = _args[13];
lean_object* v___y_919_ = _args[14];
lean_object* v___y_920_ = _args[15];
lean_object* v___y_921_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_922_; uint8_t v_clsEnabled_boxed_923_; lean_object* v_res_924_; 
v_collapsed_boxed_922_ = lean_unbox(v_collapsed_906_);
v_clsEnabled_boxed_923_ = lean_unbox(v_clsEnabled_909_);
v_res_924_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(v_cls_905_, v_collapsed_boxed_922_, v_tag_907_, v_opts_908_, v_clsEnabled_boxed_923_, v_oldTraces_910_, v_msg_911_, v_resStartStop_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec_ref(v_opts_908_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
if (lean_obj_tag(v_x_926_) == 0)
{
lean_inc(v_x_925_);
return v_x_925_;
}
else
{
lean_object* v_key_927_; lean_object* v_value_928_; lean_object* v_tail_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_key_927_ = lean_ctor_get(v_x_926_, 0);
v_value_928_ = lean_ctor_get(v_x_926_, 1);
v_tail_929_ = lean_ctor_get(v_x_926_, 2);
v___x_930_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_x_925_, v_tail_929_);
lean_inc(v_value_928_);
lean_inc(v_key_927_);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v_key_927_);
lean_ctor_set(v___x_931_, 1, v_value_928_);
v___x_932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_930_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___boxed(lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_x_933_, v_x_934_);
lean_dec(v_x_934_);
lean_dec(v_x_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(lean_object* v_as_936_, size_t v_i_937_, size_t v_stop_938_, lean_object* v_b_939_){
_start:
{
uint8_t v___x_940_; 
v___x_940_ = lean_usize_dec_eq(v_i_937_, v_stop_938_);
if (v___x_940_ == 0)
{
size_t v___x_941_; size_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_941_ = ((size_t)1ULL);
v___x_942_ = lean_usize_sub(v_i_937_, v___x_941_);
v___x_943_ = lean_array_uget_borrowed(v_as_936_, v___x_942_);
v___x_944_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_b_939_, v___x_943_);
lean_dec(v_b_939_);
v_i_937_ = v___x_942_;
v_b_939_ = v___x_944_;
goto _start;
}
else
{
return v_b_939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___boxed(lean_object* v_as_946_, lean_object* v_i_947_, lean_object* v_stop_948_, lean_object* v_b_949_){
_start:
{
size_t v_i_boxed_950_; size_t v_stop_boxed_951_; lean_object* v_res_952_; 
v_i_boxed_950_ = lean_unbox_usize(v_i_947_);
lean_dec(v_i_947_);
v_stop_boxed_951_ = lean_unbox_usize(v_stop_948_);
lean_dec(v_stop_948_);
v_res_952_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_as_946_, v_i_boxed_950_, v_stop_boxed_951_, v_b_949_);
lean_dec_ref(v_as_946_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(lean_object* v_x_960_){
_start:
{
switch(lean_obj_tag(v_x_960_))
{
case 0:
{
lean_object* v_a_961_; lean_object* v___x_962_; 
v_a_961_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v_x_960_, 1);
v___x_962_ = l_Std_Tactic_BVDecide_BVPred_toString(v_a_961_);
return v___x_962_;
}
case 1:
{
uint8_t v_a_963_; 
v_a_963_ = lean_ctor_get_uint8(v_x_960_, 0);
lean_dec_ref_known(v_x_960_, 0);
if (v_a_963_ == 0)
{
lean_object* v___x_964_; 
v___x_964_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__0));
return v___x_964_;
}
else
{
lean_object* v___x_965_; 
v___x_965_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__1));
return v___x_965_;
}
}
case 2:
{
lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_a_966_ = lean_ctor_get(v_x_960_, 0);
lean_inc_ref(v_a_966_);
lean_dec_ref_known(v_x_960_, 1);
v___x_967_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__2));
v___x_968_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_966_);
v___x_969_ = lean_string_append(v___x_967_, v___x_968_);
lean_dec_ref(v___x_968_);
return v___x_969_;
}
case 3:
{
uint8_t v_a_970_; lean_object* v_a_971_; lean_object* v_a_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_a_970_ = lean_ctor_get_uint8(v_x_960_, sizeof(void*)*2);
v_a_971_ = lean_ctor_get(v_x_960_, 0);
lean_inc_ref(v_a_971_);
v_a_972_ = lean_ctor_get(v_x_960_, 1);
lean_inc_ref(v_a_972_);
lean_dec_ref_known(v_x_960_, 2);
v___x_973_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__3));
v___x_974_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_971_);
v___x_975_ = lean_string_append(v___x_973_, v___x_974_);
lean_dec_ref(v___x_974_);
v___x_976_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4));
v___x_977_ = lean_string_append(v___x_975_, v___x_976_);
v___x_978_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_970_);
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
lean_dec_ref(v___x_978_);
v___x_980_ = lean_string_append(v___x_979_, v___x_976_);
v___x_981_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_972_);
v___x_982_ = lean_string_append(v___x_980_, v___x_981_);
lean_dec_ref(v___x_981_);
v___x_983_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__5));
v___x_984_ = lean_string_append(v___x_982_, v___x_983_);
return v___x_984_;
}
default: 
{
lean_object* v_a_985_; lean_object* v_a_986_; lean_object* v_a_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_a_985_ = lean_ctor_get(v_x_960_, 0);
lean_inc_ref(v_a_985_);
v_a_986_ = lean_ctor_get(v_x_960_, 1);
lean_inc_ref(v_a_986_);
v_a_987_ = lean_ctor_get(v_x_960_, 2);
lean_inc_ref(v_a_987_);
lean_dec_ref_known(v_x_960_, 3);
v___x_988_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__6));
v___x_989_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_985_);
v___x_990_ = lean_string_append(v___x_988_, v___x_989_);
lean_dec_ref(v___x_989_);
v___x_991_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4));
v___x_992_ = lean_string_append(v___x_990_, v___x_991_);
v___x_993_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_986_);
v___x_994_ = lean_string_append(v___x_992_, v___x_993_);
lean_dec_ref(v___x_993_);
v___x_995_ = lean_string_append(v___x_994_, v___x_991_);
v___x_996_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_987_);
v___x_997_ = lean_string_append(v___x_995_, v___x_996_);
lean_dec_ref(v___x_996_);
v___x_998_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__5));
v___x_999_ = lean_string_append(v___x_997_, v___x_998_);
return v___x_999_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(lean_object* v_a_1000_, lean_object* v_x_1001_){
_start:
{
if (lean_obj_tag(v_x_1001_) == 0)
{
uint8_t v___x_1002_; 
v___x_1002_ = 0;
return v___x_1002_;
}
else
{
lean_object* v_key_1003_; lean_object* v_tail_1004_; uint8_t v___x_1005_; 
v_key_1003_ = lean_ctor_get(v_x_1001_, 0);
v_tail_1004_ = lean_ctor_get(v_x_1001_, 2);
v___x_1005_ = lean_nat_dec_eq(v_key_1003_, v_a_1000_);
if (v___x_1005_ == 0)
{
v_x_1001_ = v_tail_1004_;
goto _start;
}
else
{
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_a_1007_, lean_object* v_x_1008_){
_start:
{
uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_res_1009_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(v_a_1007_, v_x_1008_);
lean_dec(v_x_1008_);
lean_dec(v_a_1007_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(lean_object* v_a_1011_, lean_object* v_b_1012_, lean_object* v_x_1013_){
_start:
{
if (lean_obj_tag(v_x_1013_) == 0)
{
lean_dec(v_b_1012_);
lean_dec(v_a_1011_);
return v_x_1013_;
}
else
{
lean_object* v_key_1014_; lean_object* v_value_1015_; lean_object* v_tail_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1028_; 
v_key_1014_ = lean_ctor_get(v_x_1013_, 0);
v_value_1015_ = lean_ctor_get(v_x_1013_, 1);
v_tail_1016_ = lean_ctor_get(v_x_1013_, 2);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_x_1013_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1018_ = v_x_1013_;
v_isShared_1019_ = v_isSharedCheck_1028_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_tail_1016_);
lean_inc(v_value_1015_);
lean_inc(v_key_1014_);
lean_dec(v_x_1013_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1028_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
uint8_t v___x_1020_; 
v___x_1020_ = lean_nat_dec_eq(v_key_1014_, v_a_1011_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1021_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(v_a_1011_, v_b_1012_, v_tail_1016_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 2, v___x_1021_);
v___x_1023_ = v___x_1018_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_key_1014_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_value_1015_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
else
{
lean_object* v___x_1026_; 
lean_dec(v_value_1015_);
lean_dec(v_key_1014_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v_b_1012_);
lean_ctor_set(v___x_1018_, 0, v_a_1011_);
v___x_1026_ = v___x_1018_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1011_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_b_1012_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v_tail_1016_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19___redArg(lean_object* v_x_1029_, lean_object* v_x_1030_){
_start:
{
if (lean_obj_tag(v_x_1030_) == 0)
{
return v_x_1029_;
}
else
{
lean_object* v_key_1031_; lean_object* v_value_1032_; lean_object* v_tail_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1056_; 
v_key_1031_ = lean_ctor_get(v_x_1030_, 0);
v_value_1032_ = lean_ctor_get(v_x_1030_, 1);
v_tail_1033_ = lean_ctor_get(v_x_1030_, 2);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_x_1030_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1035_ = v_x_1030_;
v_isShared_1036_ = v_isSharedCheck_1056_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_tail_1033_);
lean_inc(v_value_1032_);
lean_inc(v_key_1031_);
lean_dec(v_x_1030_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1056_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; uint64_t v___x_1038_; uint64_t v___x_1039_; uint64_t v___x_1040_; uint64_t v_fold_1041_; uint64_t v___x_1042_; uint64_t v___x_1043_; uint64_t v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1037_ = lean_array_get_size(v_x_1029_);
v___x_1038_ = lean_uint64_of_nat(v_key_1031_);
v___x_1039_ = 32ULL;
v___x_1040_ = lean_uint64_shift_right(v___x_1038_, v___x_1039_);
v_fold_1041_ = lean_uint64_xor(v___x_1038_, v___x_1040_);
v___x_1042_ = 16ULL;
v___x_1043_ = lean_uint64_shift_right(v_fold_1041_, v___x_1042_);
v___x_1044_ = lean_uint64_xor(v_fold_1041_, v___x_1043_);
v___x_1045_ = lean_uint64_to_usize(v___x_1044_);
v___x_1046_ = lean_usize_of_nat(v___x_1037_);
v___x_1047_ = ((size_t)1ULL);
v___x_1048_ = lean_usize_sub(v___x_1046_, v___x_1047_);
v___x_1049_ = lean_usize_land(v___x_1045_, v___x_1048_);
v___x_1050_ = lean_array_uget_borrowed(v_x_1029_, v___x_1049_);
lean_inc(v___x_1050_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 2, v___x_1050_);
v___x_1052_ = v___x_1035_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_key_1031_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_value_1032_);
lean_ctor_set(v_reuseFailAlloc_1055_, 2, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_array_uset(v_x_1029_, v___x_1049_, v___x_1052_);
v_x_1029_ = v___x_1053_;
v_x_1030_ = v_tail_1033_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15___redArg(lean_object* v_i_1057_, lean_object* v_source_1058_, lean_object* v_target_1059_){
_start:
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_array_get_size(v_source_1058_);
v___x_1061_ = lean_nat_dec_lt(v_i_1057_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_dec_ref(v_source_1058_);
lean_dec(v_i_1057_);
return v_target_1059_;
}
else
{
lean_object* v_es_1062_; lean_object* v___x_1063_; lean_object* v_source_1064_; lean_object* v_target_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_es_1062_ = lean_array_fget(v_source_1058_, v_i_1057_);
v___x_1063_ = lean_box(0);
v_source_1064_ = lean_array_fset(v_source_1058_, v_i_1057_, v___x_1063_);
v_target_1065_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19___redArg(v_target_1059_, v_es_1062_);
v___x_1066_ = lean_unsigned_to_nat(1u);
v___x_1067_ = lean_nat_add(v_i_1057_, v___x_1066_);
lean_dec(v_i_1057_);
v_i_1057_ = v___x_1067_;
v_source_1058_ = v_source_1064_;
v_target_1059_ = v_target_1065_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5___redArg(lean_object* v_data_1069_){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_nbuckets_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1070_ = lean_array_get_size(v_data_1069_);
v___x_1071_ = lean_unsigned_to_nat(2u);
v_nbuckets_1072_ = lean_nat_mul(v___x_1070_, v___x_1071_);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_mk_array(v_nbuckets_1072_, v___x_1074_);
v___x_1076_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15___redArg(v___x_1073_, v_data_1069_, v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1___redArg(lean_object* v_m_1077_, lean_object* v_a_1078_, lean_object* v_b_1079_){
_start:
{
lean_object* v_size_1080_; lean_object* v_buckets_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1124_; 
v_size_1080_ = lean_ctor_get(v_m_1077_, 0);
v_buckets_1081_ = lean_ctor_get(v_m_1077_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_m_1077_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1083_ = v_m_1077_;
v_isShared_1084_ = v_isSharedCheck_1124_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_buckets_1081_);
lean_inc(v_size_1080_);
lean_dec(v_m_1077_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1124_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; uint64_t v___x_1086_; uint64_t v___x_1087_; uint64_t v___x_1088_; uint64_t v_fold_1089_; uint64_t v___x_1090_; uint64_t v___x_1091_; uint64_t v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; lean_object* v_bkt_1098_; uint8_t v___x_1099_; 
v___x_1085_ = lean_array_get_size(v_buckets_1081_);
v___x_1086_ = lean_uint64_of_nat(v_a_1078_);
v___x_1087_ = 32ULL;
v___x_1088_ = lean_uint64_shift_right(v___x_1086_, v___x_1087_);
v_fold_1089_ = lean_uint64_xor(v___x_1086_, v___x_1088_);
v___x_1090_ = 16ULL;
v___x_1091_ = lean_uint64_shift_right(v_fold_1089_, v___x_1090_);
v___x_1092_ = lean_uint64_xor(v_fold_1089_, v___x_1091_);
v___x_1093_ = lean_uint64_to_usize(v___x_1092_);
v___x_1094_ = lean_usize_of_nat(v___x_1085_);
v___x_1095_ = ((size_t)1ULL);
v___x_1096_ = lean_usize_sub(v___x_1094_, v___x_1095_);
v___x_1097_ = lean_usize_land(v___x_1093_, v___x_1096_);
v_bkt_1098_ = lean_array_uget_borrowed(v_buckets_1081_, v___x_1097_);
v___x_1099_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(v_a_1078_, v_bkt_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; lean_object* v_size_x27_1101_; lean_object* v___x_1102_; lean_object* v_buckets_x27_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1100_ = lean_unsigned_to_nat(1u);
v_size_x27_1101_ = lean_nat_add(v_size_1080_, v___x_1100_);
lean_dec(v_size_1080_);
lean_inc(v_bkt_1098_);
v___x_1102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1102_, 0, v_a_1078_);
lean_ctor_set(v___x_1102_, 1, v_b_1079_);
lean_ctor_set(v___x_1102_, 2, v_bkt_1098_);
v_buckets_x27_1103_ = lean_array_uset(v_buckets_1081_, v___x_1097_, v___x_1102_);
v___x_1104_ = lean_unsigned_to_nat(4u);
v___x_1105_ = lean_nat_mul(v_size_x27_1101_, v___x_1104_);
v___x_1106_ = lean_unsigned_to_nat(3u);
v___x_1107_ = lean_nat_div(v___x_1105_, v___x_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_array_get_size(v_buckets_x27_1103_);
v___x_1109_ = lean_nat_dec_le(v___x_1107_, v___x_1108_);
lean_dec(v___x_1107_);
if (v___x_1109_ == 0)
{
lean_object* v_val_1110_; lean_object* v___x_1112_; 
v_val_1110_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5___redArg(v_buckets_x27_1103_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v_val_1110_);
lean_ctor_set(v___x_1083_, 0, v_size_x27_1101_);
v___x_1112_ = v___x_1083_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_size_x27_1101_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_val_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
else
{
lean_object* v___x_1115_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v_buckets_x27_1103_);
lean_ctor_set(v___x_1083_, 0, v_size_x27_1101_);
v___x_1115_ = v___x_1083_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_size_x27_1101_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_buckets_x27_1103_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
else
{
lean_object* v___x_1117_; lean_object* v_buckets_x27_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
lean_inc(v_bkt_1098_);
v___x_1117_ = lean_box(0);
v_buckets_x27_1118_ = lean_array_uset(v_buckets_1081_, v___x_1097_, v___x_1117_);
v___x_1119_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(v_a_1078_, v_b_1079_, v_bkt_1098_);
v___x_1120_ = lean_array_uset(v_buckets_x27_1118_, v___x_1097_, v___x_1119_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v___x_1120_);
v___x_1122_ = v___x_1083_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_size_1080_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(lean_object* v_as_x27_1125_, lean_object* v_b_1126_){
_start:
{
if (lean_obj_tag(v_as_x27_1125_) == 0)
{
return v_b_1126_;
}
else
{
lean_object* v_head_1127_; lean_object* v_tail_1128_; lean_object* v_fst_1129_; lean_object* v_snd_1130_; lean_object* v_r_1131_; 
v_head_1127_ = lean_ctor_get(v_as_x27_1125_, 0);
v_tail_1128_ = lean_ctor_get(v_as_x27_1125_, 1);
v_fst_1129_ = lean_ctor_get(v_head_1127_, 0);
v_snd_1130_ = lean_ctor_get(v_head_1127_, 1);
lean_inc(v_snd_1130_);
lean_inc(v_fst_1129_);
v_r_1131_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1___redArg(v_b_1126_, v_fst_1129_, v_snd_1130_);
v_as_x27_1125_ = v_tail_1128_;
v_b_1126_ = v_r_1131_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg___boxed(lean_object* v_as_x27_1133_, lean_object* v_b_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v_as_x27_1133_, v_b_1134_);
lean_dec(v_as_x27_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(lean_object* v_m_1136_, lean_object* v_l_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v_l_1137_, v_m_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___boxed(lean_object* v_m_1139_, lean_object* v_l_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(v_m_1139_, v_l_1140_);
lean_dec(v_l_1140_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23___redArg(lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
lean_object* v_ks_1146_; lean_object* v_vs_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1171_; 
v_ks_1146_ = lean_ctor_get(v_x_1142_, 0);
v_vs_1147_ = lean_ctor_get(v_x_1142_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_x_1142_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1149_ = v_x_1142_;
v_isShared_1150_ = v_isSharedCheck_1171_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_vs_1147_);
lean_inc(v_ks_1146_);
lean_dec(v_x_1142_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1171_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = lean_array_get_size(v_ks_1146_);
v___x_1152_ = lean_nat_dec_lt(v_x_1143_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
lean_dec(v_x_1143_);
v___x_1153_ = lean_array_push(v_ks_1146_, v_x_1144_);
v___x_1154_ = lean_array_push(v_vs_1147_, v_x_1145_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v___x_1154_);
lean_ctor_set(v___x_1149_, 0, v___x_1153_);
v___x_1156_ = v___x_1149_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
else
{
lean_object* v_k_x27_1158_; uint8_t v___x_1159_; 
v_k_x27_1158_ = lean_array_fget_borrowed(v_ks_1146_, v_x_1143_);
v___x_1159_ = l_Lean_instBEqMVarId_beq(v_x_1144_, v_k_x27_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1161_; 
if (v_isShared_1150_ == 0)
{
v___x_1161_ = v___x_1149_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_ks_1146_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_vs_1147_);
v___x_1161_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = lean_nat_add(v_x_1143_, v___x_1162_);
lean_dec(v_x_1143_);
v_x_1142_ = v___x_1161_;
v_x_1143_ = v___x_1163_;
goto _start;
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1166_ = lean_array_fset(v_ks_1146_, v_x_1143_, v_x_1144_);
v___x_1167_ = lean_array_fset(v_vs_1147_, v_x_1143_, v_x_1145_);
lean_dec(v_x_1143_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 1, v___x_1167_);
lean_ctor_set(v___x_1149_, 0, v___x_1166_);
v___x_1169_ = v___x_1149_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20___redArg(lean_object* v_n_1172_, lean_object* v_k_1173_, lean_object* v_v_1174_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23___redArg(v_n_1172_, v___x_1175_, v_k_1173_, v_v_1174_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(lean_object* v_x_1178_, size_t v_x_1179_, size_t v_x_1180_, lean_object* v_x_1181_, lean_object* v_x_1182_){
_start:
{
if (lean_obj_tag(v_x_1178_) == 0)
{
lean_object* v_es_1183_; size_t v___x_1184_; size_t v___x_1185_; lean_object* v_j_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v_es_1183_ = lean_ctor_get(v_x_1178_, 0);
v___x_1184_ = ((size_t)31ULL);
v___x_1185_ = lean_usize_land(v_x_1179_, v___x_1184_);
v_j_1186_ = lean_usize_to_nat(v___x_1185_);
v___x_1187_ = lean_array_get_size(v_es_1183_);
v___x_1188_ = lean_nat_dec_lt(v_j_1186_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_dec(v_j_1186_);
lean_dec(v_x_1182_);
lean_dec(v_x_1181_);
return v_x_1178_;
}
else
{
lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1227_; 
lean_inc_ref(v_es_1183_);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_x_1178_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; 
v_unused_1228_ = lean_ctor_get(v_x_1178_, 0);
lean_dec(v_unused_1228_);
v___x_1190_ = v_x_1178_;
v_isShared_1191_ = v_isSharedCheck_1227_;
goto v_resetjp_1189_;
}
else
{
lean_dec(v_x_1178_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1227_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_v_1192_; lean_object* v___x_1193_; lean_object* v_xs_x27_1194_; lean_object* v___y_1196_; 
v_v_1192_ = lean_array_fget(v_es_1183_, v_j_1186_);
v___x_1193_ = lean_box(0);
v_xs_x27_1194_ = lean_array_fset(v_es_1183_, v_j_1186_, v___x_1193_);
switch(lean_obj_tag(v_v_1192_))
{
case 0:
{
lean_object* v_key_1201_; lean_object* v_val_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1212_; 
v_key_1201_ = lean_ctor_get(v_v_1192_, 0);
v_val_1202_ = lean_ctor_get(v_v_1192_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_v_1192_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1204_ = v_v_1192_;
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_val_1202_);
lean_inc(v_key_1201_);
lean_dec(v_v_1192_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
uint8_t v___x_1206_; 
v___x_1206_ = l_Lean_instBEqMVarId_beq(v_x_1181_, v_key_1201_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_del_object(v___x_1204_);
v___x_1207_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1201_, v_val_1202_, v_x_1181_, v_x_1182_);
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
v___y_1196_ = v___x_1208_;
goto v___jp_1195_;
}
else
{
lean_object* v___x_1210_; 
lean_dec(v_val_1202_);
lean_dec(v_key_1201_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v_x_1182_);
lean_ctor_set(v___x_1204_, 0, v_x_1181_);
v___x_1210_ = v___x_1204_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_x_1181_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_x_1182_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
v___y_1196_ = v___x_1210_;
goto v___jp_1195_;
}
}
}
}
case 1:
{
lean_object* v_node_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1225_; 
v_node_1213_ = lean_ctor_get(v_v_1192_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_v_1192_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1215_ = v_v_1192_;
v_isShared_1216_ = v_isSharedCheck_1225_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_node_1213_);
lean_dec(v_v_1192_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1225_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
size_t v___x_1217_; size_t v___x_1218_; size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1217_ = ((size_t)5ULL);
v___x_1218_ = lean_usize_shift_right(v_x_1179_, v___x_1217_);
v___x_1219_ = ((size_t)1ULL);
v___x_1220_ = lean_usize_add(v_x_1180_, v___x_1219_);
v___x_1221_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_node_1213_, v___x_1218_, v___x_1220_, v_x_1181_, v_x_1182_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1221_);
v___x_1223_ = v___x_1215_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
v___y_1196_ = v___x_1223_;
goto v___jp_1195_;
}
}
}
default: 
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v_x_1181_);
lean_ctor_set(v___x_1226_, 1, v_x_1182_);
v___y_1196_ = v___x_1226_;
goto v___jp_1195_;
}
}
v___jp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_array_fset(v_xs_x27_1194_, v_j_1186_, v___y_1196_);
lean_dec(v_j_1186_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1197_);
v___x_1199_ = v___x_1190_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
else
{
lean_object* v_ks_1229_; lean_object* v_vs_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1248_; 
v_ks_1229_ = lean_ctor_get(v_x_1178_, 0);
v_vs_1230_ = lean_ctor_get(v_x_1178_, 1);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_x_1178_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1232_ = v_x_1178_;
v_isShared_1233_ = v_isSharedCheck_1248_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_vs_1230_);
lean_inc(v_ks_1229_);
lean_dec(v_x_1178_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1248_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_ks_1229_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_vs_1230_);
v___x_1235_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v_newNode_1236_; size_t v___x_1237_; uint8_t v___x_1238_; 
v_newNode_1236_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20___redArg(v___x_1235_, v_x_1181_, v_x_1182_);
v___x_1237_ = ((size_t)7ULL);
v___x_1238_ = lean_usize_dec_le(v___x_1237_, v_x_1180_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1239_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1236_);
v___x_1240_ = lean_unsigned_to_nat(4u);
v___x_1241_ = lean_nat_dec_lt(v___x_1239_, v___x_1240_);
lean_dec(v___x_1239_);
if (v___x_1241_ == 0)
{
lean_object* v_ks_1242_; lean_object* v_vs_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_ks_1242_ = lean_ctor_get(v_newNode_1236_, 0);
lean_inc_ref(v_ks_1242_);
v_vs_1243_ = lean_ctor_get(v_newNode_1236_, 1);
lean_inc_ref(v_vs_1243_);
lean_dec_ref(v_newNode_1236_);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0);
v___x_1246_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(v_x_1180_, v_ks_1242_, v_vs_1243_, v___x_1244_, v___x_1245_);
lean_dec_ref(v_vs_1243_);
lean_dec_ref(v_ks_1242_);
return v___x_1246_;
}
else
{
return v_newNode_1236_;
}
}
else
{
return v_newNode_1236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(size_t v_depth_1249_, lean_object* v_keys_1250_, lean_object* v_vals_1251_, lean_object* v_i_1252_, lean_object* v_entries_1253_){
_start:
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = lean_array_get_size(v_keys_1250_);
v___x_1255_ = lean_nat_dec_lt(v_i_1252_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_dec(v_i_1252_);
return v_entries_1253_;
}
else
{
lean_object* v_k_1256_; lean_object* v_v_1257_; uint64_t v___x_1258_; size_t v_h_1259_; size_t v___x_1260_; lean_object* v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; size_t v_h_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_k_1256_ = lean_array_fget_borrowed(v_keys_1250_, v_i_1252_);
v_v_1257_ = lean_array_fget_borrowed(v_vals_1251_, v_i_1252_);
v___x_1258_ = l_Lean_instHashableMVarId_hash(v_k_1256_);
v_h_1259_ = lean_uint64_to_usize(v___x_1258_);
v___x_1260_ = ((size_t)5ULL);
v___x_1261_ = lean_unsigned_to_nat(1u);
v___x_1262_ = ((size_t)1ULL);
v___x_1263_ = lean_usize_sub(v_depth_1249_, v___x_1262_);
v___x_1264_ = lean_usize_mul(v___x_1260_, v___x_1263_);
v_h_1265_ = lean_usize_shift_right(v_h_1259_, v___x_1264_);
v___x_1266_ = lean_nat_add(v_i_1252_, v___x_1261_);
lean_dec(v_i_1252_);
lean_inc(v_v_1257_);
lean_inc(v_k_1256_);
v___x_1267_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_entries_1253_, v_h_1265_, v_depth_1249_, v_k_1256_, v_v_1257_);
v_i_1252_ = v___x_1266_;
v_entries_1253_ = v___x_1267_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg___boxed(lean_object* v_depth_1269_, lean_object* v_keys_1270_, lean_object* v_vals_1271_, lean_object* v_i_1272_, lean_object* v_entries_1273_){
_start:
{
size_t v_depth_boxed_1274_; lean_object* v_res_1275_; 
v_depth_boxed_1274_ = lean_unbox_usize(v_depth_1269_);
lean_dec(v_depth_1269_);
v_res_1275_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(v_depth_boxed_1274_, v_keys_1270_, v_vals_1271_, v_i_1272_, v_entries_1273_);
lean_dec_ref(v_vals_1271_);
lean_dec_ref(v_keys_1270_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___boxed(lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
size_t v_x_40483__boxed_1281_; size_t v_x_40484__boxed_1282_; lean_object* v_res_1283_; 
v_x_40483__boxed_1281_ = lean_unbox_usize(v_x_1277_);
lean_dec(v_x_1277_);
v_x_40484__boxed_1282_ = lean_unbox_usize(v_x_1278_);
lean_dec(v_x_1278_);
v_res_1283_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_x_1276_, v_x_40483__boxed_1281_, v_x_40484__boxed_1282_, v_x_1279_, v_x_1280_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(lean_object* v_x_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_){
_start:
{
uint64_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1287_ = l_Lean_instHashableMVarId_hash(v_x_1285_);
v___x_1288_ = lean_uint64_to_usize(v___x_1287_);
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_x_1284_, v___x_1288_, v___x_1289_, v_x_1285_, v_x_1286_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(lean_object* v_mvarId_1291_, lean_object* v_val_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; lean_object* v_mctx_1296_; lean_object* v_cache_1297_; lean_object* v_zetaDeltaFVarIds_1298_; lean_object* v_postponed_1299_; lean_object* v_diag_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1329_; 
v___x_1295_ = lean_st_ref_take(v___y_1293_);
v_mctx_1296_ = lean_ctor_get(v___x_1295_, 0);
v_cache_1297_ = lean_ctor_get(v___x_1295_, 1);
v_zetaDeltaFVarIds_1298_ = lean_ctor_get(v___x_1295_, 2);
v_postponed_1299_ = lean_ctor_get(v___x_1295_, 3);
v_diag_1300_ = lean_ctor_get(v___x_1295_, 4);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1302_ = v___x_1295_;
v_isShared_1303_ = v_isSharedCheck_1329_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_diag_1300_);
lean_inc(v_postponed_1299_);
lean_inc(v_zetaDeltaFVarIds_1298_);
lean_inc(v_cache_1297_);
lean_inc(v_mctx_1296_);
lean_dec(v___x_1295_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1329_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v_depth_1304_; lean_object* v_levelAssignDepth_1305_; lean_object* v_lmvarCounter_1306_; lean_object* v_mvarCounter_1307_; lean_object* v_lDecls_1308_; lean_object* v_decls_1309_; lean_object* v_userNames_1310_; lean_object* v_lAssignment_1311_; lean_object* v_eAssignment_1312_; lean_object* v_dAssignment_1313_; lean_object* v_instanceTypedMVars_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1328_; 
v_depth_1304_ = lean_ctor_get(v_mctx_1296_, 0);
v_levelAssignDepth_1305_ = lean_ctor_get(v_mctx_1296_, 1);
v_lmvarCounter_1306_ = lean_ctor_get(v_mctx_1296_, 2);
v_mvarCounter_1307_ = lean_ctor_get(v_mctx_1296_, 3);
v_lDecls_1308_ = lean_ctor_get(v_mctx_1296_, 4);
v_decls_1309_ = lean_ctor_get(v_mctx_1296_, 5);
v_userNames_1310_ = lean_ctor_get(v_mctx_1296_, 6);
v_lAssignment_1311_ = lean_ctor_get(v_mctx_1296_, 7);
v_eAssignment_1312_ = lean_ctor_get(v_mctx_1296_, 8);
v_dAssignment_1313_ = lean_ctor_get(v_mctx_1296_, 9);
v_instanceTypedMVars_1314_ = lean_ctor_get(v_mctx_1296_, 10);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_mctx_1296_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1316_ = v_mctx_1296_;
v_isShared_1317_ = v_isSharedCheck_1328_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_instanceTypedMVars_1314_);
lean_inc(v_dAssignment_1313_);
lean_inc(v_eAssignment_1312_);
lean_inc(v_lAssignment_1311_);
lean_inc(v_userNames_1310_);
lean_inc(v_decls_1309_);
lean_inc(v_lDecls_1308_);
lean_inc(v_mvarCounter_1307_);
lean_inc(v_lmvarCounter_1306_);
lean_inc(v_levelAssignDepth_1305_);
lean_inc(v_depth_1304_);
lean_dec(v_mctx_1296_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1328_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(v_eAssignment_1312_, v_mvarId_1291_, v_val_1292_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 8, v___x_1318_);
v___x_1320_ = v___x_1316_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_depth_1304_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_levelAssignDepth_1305_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_lmvarCounter_1306_);
lean_ctor_set(v_reuseFailAlloc_1327_, 3, v_mvarCounter_1307_);
lean_ctor_set(v_reuseFailAlloc_1327_, 4, v_lDecls_1308_);
lean_ctor_set(v_reuseFailAlloc_1327_, 5, v_decls_1309_);
lean_ctor_set(v_reuseFailAlloc_1327_, 6, v_userNames_1310_);
lean_ctor_set(v_reuseFailAlloc_1327_, 7, v_lAssignment_1311_);
lean_ctor_set(v_reuseFailAlloc_1327_, 8, v___x_1318_);
lean_ctor_set(v_reuseFailAlloc_1327_, 9, v_dAssignment_1313_);
lean_ctor_set(v_reuseFailAlloc_1327_, 10, v_instanceTypedMVars_1314_);
v___x_1320_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1322_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1320_);
v___x_1322_ = v___x_1302_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_cache_1297_);
lean_ctor_set(v_reuseFailAlloc_1326_, 2, v_zetaDeltaFVarIds_1298_);
lean_ctor_set(v_reuseFailAlloc_1326_, 3, v_postponed_1299_);
lean_ctor_set(v_reuseFailAlloc_1326_, 4, v_diag_1300_);
v___x_1322_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = lean_st_ref_put(v___y_1293_, v___x_1322_);
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___boxed(lean_object* v_mvarId_1330_, lean_object* v_val_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v_mvarId_1330_, v_val_1331_, v___y_1332_);
lean_dec(v___y_1332_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
if (lean_obj_tag(v_a_1335_) == 0)
{
lean_object* v___x_1337_; 
v___x_1337_ = l_List_reverse___redArg(v_a_1336_);
return v___x_1337_;
}
else
{
lean_object* v_head_1338_; lean_object* v_snd_1339_; lean_object* v_tail_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1363_; 
v_head_1338_ = lean_ctor_get(v_a_1335_, 0);
lean_inc(v_head_1338_);
v_snd_1339_ = lean_ctor_get(v_head_1338_, 1);
lean_inc(v_snd_1339_);
v_tail_1340_ = lean_ctor_get(v_a_1335_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_a_1335_);
if (v_isSharedCheck_1363_ == 0)
{
lean_object* v_unused_1364_; 
v_unused_1364_ = lean_ctor_get(v_a_1335_, 0);
lean_dec(v_unused_1364_);
v___x_1342_ = v_a_1335_;
v_isShared_1343_ = v_isSharedCheck_1363_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_tail_1340_);
lean_dec(v_a_1335_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1363_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_fst_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1361_; 
v_fst_1344_ = lean_ctor_get(v_head_1338_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_head_1338_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v_head_1338_, 1);
lean_dec(v_unused_1362_);
v___x_1346_ = v_head_1338_;
v_isShared_1347_ = v_isSharedCheck_1361_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_fst_1344_);
lean_dec(v_head_1338_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1361_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_width_1348_; lean_object* v_atomNumber_1349_; uint8_t v_synthetic_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v_width_1348_ = lean_ctor_get(v_snd_1339_, 0);
lean_inc(v_width_1348_);
v_atomNumber_1349_ = lean_ctor_get(v_snd_1339_, 1);
lean_inc(v_atomNumber_1349_);
v_synthetic_1350_ = lean_ctor_get_uint8(v_snd_1339_, sizeof(void*)*2);
lean_dec(v_snd_1339_);
v___x_1351_ = lean_box(v_synthetic_1350_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v___x_1351_);
v___x_1353_ = v___x_1346_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_fst_1344_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v_width_1348_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_atomNumber_1349_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v_a_1336_);
lean_ctor_set(v___x_1342_, 0, v___x_1355_);
v___x_1357_ = v___x_1342_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_a_1336_);
v___x_1357_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
v_a_1335_ = v_tail_1340_;
v_a_1336_ = v___x_1357_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(lean_object* v_cls_1368_, lean_object* v_msg_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_ref_1375_; lean_object* v___x_1376_; lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1421_; 
v_ref_1375_ = lean_ctor_get(v___y_1372_, 4);
v___x_1376_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1421_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1421_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v_traceState_1382_; lean_object* v_env_1383_; lean_object* v_nextMacroScope_1384_; lean_object* v_ngen_1385_; lean_object* v_auxDeclNGen_1386_; lean_object* v_cache_1387_; lean_object* v_messages_1388_; lean_object* v_infoState_1389_; lean_object* v_snapshotTasks_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1420_; 
v___x_1381_ = lean_st_ref_take(v___y_1373_);
v_traceState_1382_ = lean_ctor_get(v___x_1381_, 4);
v_env_1383_ = lean_ctor_get(v___x_1381_, 0);
v_nextMacroScope_1384_ = lean_ctor_get(v___x_1381_, 1);
v_ngen_1385_ = lean_ctor_get(v___x_1381_, 2);
v_auxDeclNGen_1386_ = lean_ctor_get(v___x_1381_, 3);
v_cache_1387_ = lean_ctor_get(v___x_1381_, 5);
v_messages_1388_ = lean_ctor_get(v___x_1381_, 6);
v_infoState_1389_ = lean_ctor_get(v___x_1381_, 7);
v_snapshotTasks_1390_ = lean_ctor_get(v___x_1381_, 8);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1392_ = v___x_1381_;
v_isShared_1393_ = v_isSharedCheck_1420_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_snapshotTasks_1390_);
lean_inc(v_infoState_1389_);
lean_inc(v_messages_1388_);
lean_inc(v_cache_1387_);
lean_inc(v_traceState_1382_);
lean_inc(v_auxDeclNGen_1386_);
lean_inc(v_ngen_1385_);
lean_inc(v_nextMacroScope_1384_);
lean_inc(v_env_1383_);
lean_dec(v___x_1381_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1420_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
uint64_t v_tid_1394_; lean_object* v_traces_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1419_; 
v_tid_1394_ = lean_ctor_get_uint64(v_traceState_1382_, sizeof(void*)*1);
v_traces_1395_ = lean_ctor_get(v_traceState_1382_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_traceState_1382_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1397_ = v_traceState_1382_;
v_isShared_1398_ = v_isSharedCheck_1419_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_traces_1395_);
lean_dec(v_traceState_1382_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1419_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; double v___x_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0);
v___x_1401_ = 0;
v___x_1402_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0));
v___x_1403_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1403_, 0, v_cls_1368_);
lean_ctor_set(v___x_1403_, 1, v___x_1399_);
lean_ctor_set(v___x_1403_, 2, v___x_1402_);
lean_ctor_set_float(v___x_1403_, sizeof(void*)*3, v___x_1400_);
lean_ctor_set_float(v___x_1403_, sizeof(void*)*3 + 8, v___x_1400_);
lean_ctor_set_uint8(v___x_1403_, sizeof(void*)*3 + 16, v___x_1401_);
v___x_1404_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1));
v___x_1405_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1403_);
lean_ctor_set(v___x_1405_, 1, v_a_1377_);
lean_ctor_set(v___x_1405_, 2, v___x_1404_);
lean_inc(v_ref_1375_);
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_ref_1375_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = l_Lean_PersistentArray_push___redArg(v_traces_1395_, v___x_1406_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1407_);
v___x_1409_ = v___x_1397_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1407_);
lean_ctor_set_uint64(v_reuseFailAlloc_1418_, sizeof(void*)*1, v_tid_1394_);
v___x_1409_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1411_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v___x_1409_);
v___x_1411_ = v___x_1392_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_env_1383_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_nextMacroScope_1384_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_ngen_1385_);
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_auxDeclNGen_1386_);
lean_ctor_set(v_reuseFailAlloc_1417_, 4, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1417_, 5, v_cache_1387_);
lean_ctor_set(v_reuseFailAlloc_1417_, 6, v_messages_1388_);
lean_ctor_set(v_reuseFailAlloc_1417_, 7, v_infoState_1389_);
lean_ctor_set(v_reuseFailAlloc_1417_, 8, v_snapshotTasks_1390_);
v___x_1411_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1412_ = lean_st_ref_put(v___y_1373_, v___x_1411_);
v___x_1413_ = lean_box(0);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1413_);
v___x_1415_ = v___x_1379_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___boxed(lean_object* v_cls_1422_, lean_object* v_msg_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(v_cls_1422_, v_msg_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1429_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = lean_unsigned_to_nat(16u);
v___x_1432_ = lean_mk_array(v___x_1431_, v___x_1430_);
return v___x_1432_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0);
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
lean_ctor_set(v___x_1435_, 1, v___x_1433_);
return v___x_1435_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4));
v___x_1441_ = l_Lean_stringToMessageData(v___x_1440_);
return v___x_1441_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1442_; double v___x_1443_; 
v___x_1442_ = lean_unsigned_to_nat(1000000000u);
v___x_1443_ = lean_float_of_nat(v___x_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(lean_object* v_unsatProver_1444_, lean_object* v_g_1445_, lean_object* v_cls_1446_, uint8_t v___x_1447_, lean_object* v___x_1448_, lean_object* v___f_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v_options_1549_; lean_object* v_toCold_1550_; uint8_t v_hasTrace_1551_; lean_object* v___y_1553_; 
v_options_1549_ = lean_ctor_get(v___y_1456_, 1);
v_toCold_1550_ = lean_ctor_get(v___y_1456_, 0);
v_hasTrace_1551_ = lean_ctor_get_uint8(v_options_1549_, sizeof(void*)*1);
if (v_hasTrace_1551_ == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref(v___f_1449_);
lean_dec_ref(v___x_1448_);
lean_inc(v_g_1445_);
v___x_1583_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1445_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
v___y_1553_ = v___x_1583_;
goto v___jp_1552_;
}
else
{
lean_object* v_inheritedTraceOptions_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v_a_1591_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v_a_1606_; 
v_inheritedTraceOptions_1584_ = lean_ctor_get(v_toCold_1550_, 4);
v___x_1585_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3));
lean_inc(v_cls_1446_);
v___x_1586_ = l_Lean_Name_append(v___x_1585_, v_cls_1446_);
v___x_1587_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1584_, v_options_1549_, v___x_1586_);
lean_dec(v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = l_Lean_trace_profiler;
v___x_1657_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_options_1549_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec_ref(v___f_1449_);
lean_dec_ref(v___x_1448_);
lean_inc(v_g_1445_);
v___x_1658_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1445_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
v___y_1553_ = v___x_1658_;
goto v___jp_1552_;
}
else
{
goto v___jp_1615_;
}
}
else
{
goto v___jp_1615_;
}
v___jp_1588_:
{
lean_object* v___x_1592_; double v___x_1593_; double v___x_1594_; double v___x_1595_; double v___x_1596_; double v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1592_ = lean_io_mono_nanos_now();
v___x_1593_ = lean_float_of_nat(v___y_1590_);
v___x_1594_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6);
v___x_1595_ = lean_float_div(v___x_1593_, v___x_1594_);
v___x_1596_ = lean_float_of_nat(v___x_1592_);
v___x_1597_ = lean_float_div(v___x_1596_, v___x_1594_);
v___x_1598_ = lean_box_float(v___x_1595_);
v___x_1599_ = lean_box_float(v___x_1597_);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1598_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v_a_1591_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
lean_inc(v_cls_1446_);
v___x_1602_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(v_cls_1446_, v___x_1447_, v___x_1448_, v_options_1549_, v___x_1587_, v___y_1589_, v___f_1449_, v___x_1601_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
v___y_1553_ = v___x_1602_;
goto v___jp_1552_;
}
v___jp_1603_:
{
lean_object* v___x_1607_; double v___x_1608_; double v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1607_ = lean_io_get_num_heartbeats();
v___x_1608_ = lean_float_of_nat(v___y_1605_);
v___x_1609_ = lean_float_of_nat(v___x_1607_);
v___x_1610_ = lean_box_float(v___x_1608_);
v___x_1611_ = lean_box_float(v___x_1609_);
v___x_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v_a_1606_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
lean_inc(v_cls_1446_);
v___x_1614_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(v_cls_1446_, v___x_1447_, v___x_1448_, v_options_1549_, v___x_1587_, v___y_1604_, v___f_1449_, v___x_1613_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
v___y_1553_ = v___x_1614_;
goto v___jp_1552_;
}
v___jp_1615_:
{
lean_object* v___x_1616_; lean_object* v_a_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1616_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(v___y_1457_);
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1619_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_options_1549_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_io_mono_nanos_now();
lean_inc(v_g_1445_);
v___x_1621_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1445_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set_tag(v___x_1624_, 1);
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
v___y_1589_ = v_a_1617_;
v___y_1590_ = v___x_1620_;
v_a_1591_ = v___x_1627_;
goto v___jp_1588_;
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
v_a_1630_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1621_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1621_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set_tag(v___x_1632_, 0);
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
v___y_1589_ = v_a_1617_;
v___y_1590_ = v___x_1620_;
v_a_1591_ = v___x_1635_;
goto v___jp_1588_;
}
}
}
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_io_get_num_heartbeats();
lean_inc(v_g_1445_);
v___x_1639_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1445_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 1);
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
v___y_1604_ = v_a_1617_;
v___y_1605_ = v___x_1638_;
v_a_1606_ = v___x_1645_;
goto v___jp_1603_;
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
v_a_1648_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1639_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1639_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set_tag(v___x_1650_, 0);
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
v___y_1604_ = v_a_1617_;
v___y_1605_ = v___x_1638_;
v_a_1606_ = v___x_1653_;
goto v___jp_1603_;
}
}
}
}
}
}
v___jp_1459_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1470_ = lean_box(0);
v___x_1471_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v___y_1469_, v___x_1470_);
v___x_1472_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1);
v___x_1473_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v___x_1471_, v___x_1472_);
lean_dec(v___x_1471_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1461_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc_ref(v___y_1466_);
lean_inc(v_g_1445_);
v___x_1474_ = lean_apply_8(v_unsatProver_1444_, v_g_1445_, v___y_1466_, v___x_1473_, v___y_1464_, v___y_1465_, v___y_1461_, v___y_1463_, lean_box(0));
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1520_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1520_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1520_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
if (lean_obj_tag(v_a_1475_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v___y_1466_);
lean_dec(v_g_1445_);
v_a_1479_ = lean_ctor_get(v_a_1475_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_a_1475_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1481_ = v_a_1475_;
v_isShared_1482_ = v_isSharedCheck_1489_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v_a_1475_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1489_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1484_);
v___x_1486_ = v___x_1477_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1519_; 
lean_del_object(v___x_1477_);
v_a_1490_ = lean_ctor_get(v_a_1475_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_a_1475_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1492_ = v_a_1475_;
v_isShared_1493_ = v_isSharedCheck_1519_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v_a_1475_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1519_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_proof_1494_; lean_object* v_cert_1495_; lean_object* v_proveFalse_1496_; lean_object* v___x_1497_; 
v_proof_1494_ = lean_ctor_get(v_a_1490_, 0);
lean_inc_ref(v_proof_1494_);
v_cert_1495_ = lean_ctor_get(v_a_1490_, 1);
lean_inc(v_cert_1495_);
lean_dec(v_a_1490_);
v_proveFalse_1496_ = lean_ctor_get(v___y_1466_, 1);
lean_inc_ref(v_proveFalse_1496_);
lean_dec_ref(v___y_1466_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1461_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1462_);
lean_inc_ref(v___y_1468_);
v___x_1497_ = lean_apply_10(v_proveFalse_1496_, v_proof_1494_, v___y_1468_, v___y_1462_, v___y_1460_, v___y_1467_, v___y_1464_, v___y_1465_, v___y_1461_, v___y_1463_, lean_box(0));
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1509_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1499_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v_g_1445_, v_a_1498_, v___y_1465_);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v___x_1499_, 0);
lean_dec(v_unused_1510_);
v___x_1501_ = v___x_1499_;
v_isShared_1502_ = v_isSharedCheck_1509_;
goto v_resetjp_1500_;
}
else
{
lean_dec(v___x_1499_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1509_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v_cert_1495_);
v___x_1504_ = v___x_1492_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_cert_1495_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1504_);
v___x_1506_ = v___x_1501_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec(v_cert_1495_);
lean_del_object(v___x_1492_);
lean_dec(v_g_1445_);
v_a_1511_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1497_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1497_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec_ref(v___y_1466_);
lean_dec(v_g_1445_);
v_a_1521_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1474_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1474_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
v___jp_1529_:
{
lean_object* v___x_1539_; lean_object* v_atoms_1540_; lean_object* v_buckets_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1539_ = lean_st_ref_get(v___y_1532_);
v_atoms_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc_ref(v_atoms_1540_);
lean_dec(v___x_1539_);
v_buckets_1541_ = lean_ctor_get(v_atoms_1540_, 1);
lean_inc_ref(v_buckets_1541_);
lean_dec_ref(v_atoms_1540_);
v___x_1542_ = lean_box(0);
v___x_1543_ = lean_array_get_size(v_buckets_1541_);
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_nat_dec_lt(v___x_1544_, v___x_1543_);
if (v___x_1545_ == 0)
{
lean_dec_ref(v_buckets_1541_);
v___y_1460_ = v___y_1533_;
v___y_1461_ = v___y_1537_;
v___y_1462_ = v___y_1532_;
v___y_1463_ = v___y_1538_;
v___y_1464_ = v___y_1535_;
v___y_1465_ = v___y_1536_;
v___y_1466_ = v___y_1530_;
v___y_1467_ = v___y_1534_;
v___y_1468_ = v___y_1531_;
v___y_1469_ = v___x_1542_;
goto v___jp_1459_;
}
else
{
size_t v___x_1546_; size_t v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = lean_usize_of_nat(v___x_1543_);
v___x_1547_ = ((size_t)0ULL);
v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_buckets_1541_, v___x_1546_, v___x_1547_, v___x_1542_);
lean_dec_ref(v_buckets_1541_);
v___y_1460_ = v___y_1533_;
v___y_1461_ = v___y_1537_;
v___y_1462_ = v___y_1532_;
v___y_1463_ = v___y_1538_;
v___y_1464_ = v___y_1535_;
v___y_1465_ = v___y_1536_;
v___y_1466_ = v___y_1530_;
v___y_1467_ = v___y_1534_;
v___y_1468_ = v___y_1531_;
v___y_1469_ = v___x_1548_;
goto v___jp_1459_;
}
}
v___jp_1552_:
{
if (lean_obj_tag(v___y_1553_) == 0)
{
if (v_hasTrace_1551_ == 0)
{
lean_object* v_a_1554_; 
lean_dec(v_cls_1446_);
v_a_1554_ = lean_ctor_get(v___y_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___y_1553_, 1);
v___y_1530_ = v_a_1554_;
v___y_1531_ = v___y_1450_;
v___y_1532_ = v___y_1451_;
v___y_1533_ = v___y_1452_;
v___y_1534_ = v___y_1453_;
v___y_1535_ = v___y_1454_;
v___y_1536_ = v___y_1455_;
v___y_1537_ = v___y_1456_;
v___y_1538_ = v___y_1457_;
goto v___jp_1529_;
}
else
{
lean_object* v_a_1555_; lean_object* v_inheritedTraceOptions_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_a_1555_ = lean_ctor_get(v___y_1553_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___y_1553_, 1);
v_inheritedTraceOptions_1556_ = lean_ctor_get(v_toCold_1550_, 4);
v___x_1557_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3));
lean_inc(v_cls_1446_);
v___x_1558_ = l_Lean_Name_append(v___x_1557_, v_cls_1446_);
v___x_1559_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1556_, v_options_1549_, v___x_1558_);
lean_dec(v___x_1558_);
if (v___x_1559_ == 0)
{
lean_dec(v_cls_1446_);
v___y_1530_ = v_a_1555_;
v___y_1531_ = v___y_1450_;
v___y_1532_ = v___y_1451_;
v___y_1533_ = v___y_1452_;
v___y_1534_ = v___y_1453_;
v___y_1535_ = v___y_1454_;
v___y_1536_ = v___y_1455_;
v___y_1537_ = v___y_1456_;
v___y_1538_ = v___y_1457_;
goto v___jp_1529_;
}
else
{
lean_object* v_bvExpr_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_bvExpr_1560_ = lean_ctor_get(v_a_1555_, 0);
v___x_1561_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5);
lean_inc_ref(v_bvExpr_1560_);
v___x_1562_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_bvExpr_1560_);
v___x_1563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
v___x_1564_ = l_Lean_MessageData_ofFormat(v___x_1563_);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1561_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(v_cls_1446_, v___x_1565_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_dec_ref_known(v___x_1566_, 1);
v___y_1530_ = v_a_1555_;
v___y_1531_ = v___y_1450_;
v___y_1532_ = v___y_1451_;
v___y_1533_ = v___y_1452_;
v___y_1534_ = v___y_1453_;
v___y_1535_ = v___y_1454_;
v___y_1536_ = v___y_1455_;
v___y_1537_ = v___y_1456_;
v___y_1538_ = v___y_1457_;
goto v___jp_1529_;
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v_a_1555_);
lean_dec(v_g_1445_);
lean_dec_ref(v_unsatProver_1444_);
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec(v_cls_1446_);
lean_dec(v_g_1445_);
lean_dec_ref(v_unsatProver_1444_);
v_a_1575_ = lean_ctor_get(v___y_1553_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___y_1553_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___y_1553_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___y_1553_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed(lean_object* v_unsatProver_1659_, lean_object* v_g_1660_, lean_object* v_cls_1661_, lean_object* v___x_1662_, lean_object* v___x_1663_, lean_object* v___f_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
uint8_t v___x_40882__boxed_1674_; lean_object* v_res_1675_; 
v___x_40882__boxed_1674_ = lean_unbox(v___x_1662_);
v_res_1675_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(v_unsatProver_1659_, v_g_1660_, v_cls_1661_, v___x_40882__boxed_1674_, v___x_1663_, v___f_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(lean_object* v_g_1684_, lean_object* v_unsatProver_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___f_1695_; lean_object* v_cls_1696_; uint8_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___f_1700_; lean_object* v___x_1701_; 
v___f_1695_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0));
v_cls_1696_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4));
v___x_1697_ = 1;
v___x_1698_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0));
v___x_1699_ = lean_box(v___x_1697_);
lean_inc(v_g_1684_);
v___f_1700_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed), 15, 6);
lean_closure_set(v___f_1700_, 0, v_unsatProver_1685_);
lean_closure_set(v___f_1700_, 1, v_g_1684_);
lean_closure_set(v___f_1700_, 2, v_cls_1696_);
lean_closure_set(v___f_1700_, 3, v___x_1699_);
lean_closure_set(v___f_1700_, 4, v___x_1698_);
lean_closure_set(v___f_1700_, 5, v___f_1695_);
v___x_1701_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_g_1684_, v___f_1700_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___boxed(lean_object* v_g_1702_, lean_object* v_unsatProver_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1702_, v_unsatProver_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(lean_object* v_00_u03b1_1714_, lean_object* v_g_1715_, lean_object* v_unsatProver_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1715_, v_unsatProver_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed(lean_object* v_00_u03b1_1727_, lean_object* v_g_1728_, lean_object* v_unsatProver_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(v_00_u03b1_1727_, v_g_1728_, v_unsatProver_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(lean_object* v_mvarId_1740_, lean_object* v_val_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v_mvarId_1740_, v_val_1741_, v___y_1747_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___boxed(lean_object* v_mvarId_1752_, lean_object* v_val_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(v_mvarId_1752_, v_val_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6(lean_object* v_cls_1764_, lean_object* v_msg_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(v_cls_1764_, v_msg_1765_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___boxed(lean_object* v_cls_1776_, lean_object* v_msg_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6(v_cls_1776_, v_msg_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13(lean_object* v_00_u03b1_1788_, lean_object* v_x_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_x_1789_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1800_, lean_object* v_x_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13(v_00_u03b1_1800_, v_x_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1(lean_object* v_00_u03b2_1812_, lean_object* v_m_1813_, lean_object* v_a_1814_, lean_object* v_b_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1___redArg(v_m_1813_, v_a_1814_, v_b_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2(lean_object* v_as_1817_, lean_object* v_as_x27_1818_, lean_object* v_b_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v_as_x27_1818_, v_b_1819_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___boxed(lean_object* v_as_1822_, lean_object* v_as_x27_1823_, lean_object* v_b_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2(v_as_1822_, v_as_x27_1823_, v_b_1824_, v_a_1825_);
lean_dec(v_as_x27_1823_);
lean_dec(v_as_1822_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4(lean_object* v_00_u03b2_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_, lean_object* v_x_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(v_x_1828_, v_x_1829_, v_x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12(lean_object* v_oldTraces_1832_, lean_object* v_data_1833_, lean_object* v_ref_1834_, lean_object* v_msg_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg(v_oldTraces_1832_, v_data_1833_, v_ref_1834_, v_msg_1835_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___boxed(lean_object* v_oldTraces_1846_, lean_object* v_data_1847_, lean_object* v_ref_1848_, lean_object* v_msg_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12(v_oldTraces_1846_, v_data_1847_, v_ref_1848_, v_msg_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1859_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_1860_, lean_object* v_a_1861_, lean_object* v_x_1862_){
_start:
{
uint8_t v___x_1863_; 
v___x_1863_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(v_a_1861_, v_x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1864_, lean_object* v_a_1865_, lean_object* v_x_1866_){
_start:
{
uint8_t v_res_1867_; lean_object* v_r_1868_; 
v_res_1867_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4(v_00_u03b2_1864_, v_a_1865_, v_x_1866_);
lean_dec(v_x_1866_);
lean_dec(v_a_1865_);
v_r_1868_ = lean_box(v_res_1867_);
return v_r_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_1869_, lean_object* v_data_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5___redArg(v_data_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_1872_, lean_object* v_a_1873_, lean_object* v_b_1874_, lean_object* v_x_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(v_a_1873_, v_b_1874_, v_x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10(lean_object* v_00_u03b2_1877_, lean_object* v_x_1878_, size_t v_x_1879_, size_t v_x_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_x_1878_, v_x_1879_, v_x_1880_, v_x_1881_, v_x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___boxed(lean_object* v_00_u03b2_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
size_t v_x_41513__boxed_1890_; size_t v_x_41514__boxed_1891_; lean_object* v_res_1892_; 
v_x_41513__boxed_1890_ = lean_unbox_usize(v_x_1886_);
lean_dec(v_x_1886_);
v_x_41514__boxed_1891_ = lean_unbox_usize(v_x_1887_);
lean_dec(v_x_1887_);
v_res_1892_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10(v_00_u03b2_1884_, v_x_1885_, v_x_41513__boxed_1890_, v_x_41514__boxed_1891_, v_x_1888_, v_x_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15(lean_object* v_00_u03b2_1893_, lean_object* v_i_1894_, lean_object* v_source_1895_, lean_object* v_target_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15___redArg(v_i_1894_, v_source_1895_, v_target_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20(lean_object* v_00_u03b2_1898_, lean_object* v_n_1899_, lean_object* v_k_1900_, lean_object* v_v_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20___redArg(v_n_1899_, v_k_1900_, v_v_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21(lean_object* v_00_u03b2_1903_, size_t v_depth_1904_, lean_object* v_keys_1905_, lean_object* v_vals_1906_, lean_object* v_heq_1907_, lean_object* v_i_1908_, lean_object* v_entries_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(v_depth_1904_, v_keys_1905_, v_vals_1906_, v_i_1908_, v_entries_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___boxed(lean_object* v_00_u03b2_1911_, lean_object* v_depth_1912_, lean_object* v_keys_1913_, lean_object* v_vals_1914_, lean_object* v_heq_1915_, lean_object* v_i_1916_, lean_object* v_entries_1917_){
_start:
{
size_t v_depth_boxed_1918_; lean_object* v_res_1919_; 
v_depth_boxed_1918_ = lean_unbox_usize(v_depth_1912_);
lean_dec(v_depth_1912_);
v_res_1919_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21(v_00_u03b2_1911_, v_depth_boxed_1918_, v_keys_1913_, v_vals_1914_, v_heq_1915_, v_i_1916_, v_entries_1917_);
lean_dec_ref(v_vals_1914_);
lean_dec_ref(v_keys_1913_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19(lean_object* v_00_u03b2_1920_, lean_object* v_x_1921_, lean_object* v_x_1922_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19___redArg(v_x_1921_, v_x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23(lean_object* v_00_u03b2_1924_, lean_object* v_x_1925_, lean_object* v_x_1926_, lean_object* v_x_1927_, lean_object* v_x_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23___redArg(v_x_1925_, v_x_1926_, v_x_1927_, v_x_1928_);
return v___x_1929_;
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
