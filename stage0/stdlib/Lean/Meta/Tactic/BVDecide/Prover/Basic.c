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
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_nbuckets_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_184_ = lean_array_get_size(v_data_183_);
v___x_185_ = lean_unsigned_to_nat(2u);
v_nbuckets_186_ = lean_nat_mul(v___x_184_, v___x_185_);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = lean_box(0);
v___x_189_ = lean_mk_array(v_nbuckets_186_, v___x_188_);
v___x_190_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v___x_187_, v_data_183_, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(lean_object* v_m_191_, lean_object* v_a_192_, lean_object* v_b_193_){
_start:
{
lean_object* v_size_194_; lean_object* v_buckets_195_; lean_object* v_type_196_; lean_object* v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; uint64_t v___x_200_; uint64_t v_fold_201_; uint64_t v___x_202_; uint64_t v___x_203_; uint64_t v___x_204_; size_t v___x_205_; size_t v___x_206_; size_t v___x_207_; size_t v___x_208_; size_t v___x_209_; lean_object* v_bkt_210_; uint8_t v___x_211_; 
v_size_194_ = lean_ctor_get(v_m_191_, 0);
v_buckets_195_ = lean_ctor_get(v_m_191_, 1);
v_type_196_ = lean_ctor_get(v_a_192_, 1);
v___x_197_ = lean_array_get_size(v_buckets_195_);
v___x_198_ = l_Lean_Expr_hash(v_type_196_);
v___x_199_ = 32ULL;
v___x_200_ = lean_uint64_shift_right(v___x_198_, v___x_199_);
v_fold_201_ = lean_uint64_xor(v___x_198_, v___x_200_);
v___x_202_ = 16ULL;
v___x_203_ = lean_uint64_shift_right(v_fold_201_, v___x_202_);
v___x_204_ = lean_uint64_xor(v_fold_201_, v___x_203_);
v___x_205_ = lean_uint64_to_usize(v___x_204_);
v___x_206_ = lean_usize_of_nat(v___x_197_);
v___x_207_ = ((size_t)1ULL);
v___x_208_ = lean_usize_sub(v___x_206_, v___x_207_);
v___x_209_ = lean_usize_land(v___x_205_, v___x_208_);
v_bkt_210_ = lean_array_uget_borrowed(v_buckets_195_, v___x_209_);
v___x_211_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_192_, v_bkt_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_232_; 
lean_inc_ref(v_buckets_195_);
lean_inc(v_size_194_);
v_isSharedCheck_232_ = !lean_is_exclusive(v_m_191_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; lean_object* v_unused_234_; 
v_unused_233_ = lean_ctor_get(v_m_191_, 1);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_m_191_, 0);
lean_dec(v_unused_234_);
v___x_213_ = v_m_191_;
v_isShared_214_ = v_isSharedCheck_232_;
goto v_resetjp_212_;
}
else
{
lean_dec(v_m_191_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_232_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v_size_x27_216_; lean_object* v___x_217_; lean_object* v_buckets_x27_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_215_ = lean_unsigned_to_nat(1u);
v_size_x27_216_ = lean_nat_add(v_size_194_, v___x_215_);
lean_dec(v_size_194_);
lean_inc(v_bkt_210_);
v___x_217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_217_, 0, v_a_192_);
lean_ctor_set(v___x_217_, 1, v_b_193_);
lean_ctor_set(v___x_217_, 2, v_bkt_210_);
v_buckets_x27_218_ = lean_array_uset(v_buckets_195_, v___x_209_, v___x_217_);
v___x_219_ = lean_unsigned_to_nat(4u);
v___x_220_ = lean_nat_mul(v_size_x27_216_, v___x_219_);
v___x_221_ = lean_unsigned_to_nat(3u);
v___x_222_ = lean_nat_div(v___x_220_, v___x_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_array_get_size(v_buckets_x27_218_);
v___x_224_ = lean_nat_dec_le(v___x_222_, v___x_223_);
lean_dec(v___x_222_);
if (v___x_224_ == 0)
{
lean_object* v_val_225_; lean_object* v___x_227_; 
v_val_225_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_buckets_x27_218_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v_val_225_);
lean_ctor_set(v___x_213_, 0, v_size_x27_216_);
v___x_227_ = v___x_213_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_size_x27_216_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_val_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
else
{
lean_object* v___x_230_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v_buckets_x27_218_);
lean_ctor_set(v___x_213_, 0, v_size_x27_216_);
v___x_230_ = v___x_213_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_size_x27_216_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_buckets_x27_218_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_dec(v_b_193_);
lean_dec_ref(v_a_192_);
return v_m_191_;
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_box(0);
v___x_239_ = lean_unsigned_to_nat(16u);
v___x_240_ = lean_mk_array(v___x_239_, v___x_238_);
return v___x_240_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__2);
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
return v___x_243_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4(void){
_start:
{
lean_object* v___x_244_; lean_object* v_sats_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__3);
v_sats_245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1));
v___x_246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_246_, 0, v_sats_245_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
lean_ctor_set(v___x_246_, 2, v___x_244_);
lean_ctor_set(v___x_246_, 3, v___x_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(lean_object* v_as_247_, size_t v_sz_248_, size_t v_i_249_, lean_object* v_b_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_a_261_; uint8_t v___x_265_; 
v___x_265_ = lean_usize_dec_lt(v_i_249_, v_sz_248_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v_b_250_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__0));
v___x_268_ = l_Lean_Core_checkSystem(v___x_267_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec_ref_known(v___x_268_, 1);
v_a_269_ = lean_array_uget_borrowed(v_as_247_, v_i_249_);
lean_inc(v_a_269_);
v___x_270_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed), 11, 1);
lean_closure_set(v___x_270_, 0, v_a_269_);
v___x_271_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__4);
v___x_272_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v___x_270_, v___x_271_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v_fst_274_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v___x_272_, 1);
v_fst_274_ = lean_ctor_get(v_a_273_, 0);
lean_inc(v_fst_274_);
if (lean_obj_tag(v_fst_274_) == 1)
{
lean_object* v_snd_275_; lean_object* v_fst_276_; lean_object* v_snd_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_287_; 
v_snd_275_ = lean_ctor_get(v_a_273_, 1);
lean_inc(v_snd_275_);
lean_dec(v_a_273_);
v_fst_276_ = lean_ctor_get(v_b_250_, 0);
v_snd_277_ = lean_ctor_get(v_b_250_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_b_250_);
if (v_isSharedCheck_287_ == 0)
{
v___x_279_ = v_b_250_;
v_isShared_280_ = v_isSharedCheck_287_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_snd_277_);
lean_inc(v_fst_276_);
lean_dec(v_b_250_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_287_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v_val_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v_val_281_ = lean_ctor_get(v_fst_274_, 0);
lean_inc(v_val_281_);
lean_dec_ref_known(v_fst_274_, 1);
v___x_282_ = l_Array_append___redArg(v_fst_276_, v_snd_275_);
lean_dec(v_snd_275_);
v___x_283_ = lean_array_push(v___x_282_, v_val_281_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_283_);
v___x_285_ = v___x_279_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_snd_277_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
v_a_261_ = v___x_285_;
goto v___jp_260_;
}
}
}
else
{
lean_object* v_fst_288_; lean_object* v_snd_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_298_; 
lean_dec(v_fst_274_);
lean_dec(v_a_273_);
v_fst_288_ = lean_ctor_get(v_b_250_, 0);
v_snd_289_ = lean_ctor_get(v_b_250_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_b_250_);
if (v_isSharedCheck_298_ == 0)
{
v___x_291_ = v_b_250_;
v_isShared_292_ = v_isSharedCheck_298_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_snd_289_);
lean_inc(v_fst_288_);
lean_dec(v_b_250_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_298_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_293_ = lean_box(0);
lean_inc(v_a_269_);
v___x_294_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_snd_289_, v_a_269_, v___x_293_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v___x_294_);
v___x_296_ = v___x_291_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_fst_288_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
v_a_261_ = v___x_296_;
goto v___jp_260_;
}
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec_ref(v_b_250_);
v_a_299_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_272_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_272_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec_ref(v_b_250_);
v_a_307_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_268_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_268_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
v___jp_260_:
{
size_t v___x_262_; size_t v___x_263_; 
v___x_262_ = ((size_t)1ULL);
v___x_263_ = lean_usize_add(v_i_249_, v___x_262_);
v_i_249_ = v___x_263_;
v_b_250_ = v_a_261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___boxed(lean_object* v_as_315_, lean_object* v_sz_316_, lean_object* v_i_317_, lean_object* v_b_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
size_t v_sz_boxed_328_; size_t v_i_boxed_329_; lean_object* v_res_330_; 
v_sz_boxed_328_ = lean_unbox_usize(v_sz_316_);
lean_dec(v_sz_316_);
v_i_boxed_329_ = lean_unbox_usize(v_i_317_);
lean_dec(v_i_317_);
v_res_330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v_as_315_, v_sz_boxed_328_, v_i_boxed_329_, v_b_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec_ref(v_as_315_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(lean_object* v_a_331_, lean_object* v_b_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_array_340_; lean_object* v_start_341_; lean_object* v_stop_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_357_; 
v_array_340_ = lean_ctor_get(v_a_331_, 0);
v_start_341_ = lean_ctor_get(v_a_331_, 1);
v_stop_342_ = lean_ctor_get(v_a_331_, 2);
v_isSharedCheck_357_ = !lean_is_exclusive(v_a_331_);
if (v_isSharedCheck_357_ == 0)
{
v___x_344_ = v_a_331_;
v_isShared_345_ = v_isSharedCheck_357_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_stop_342_);
lean_inc(v_start_341_);
lean_inc(v_array_340_);
lean_dec(v_a_331_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_357_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
uint8_t v___x_346_; 
v___x_346_ = lean_nat_dec_lt(v_start_341_, v_stop_342_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_del_object(v___x_344_);
lean_dec(v_stop_342_);
lean_dec(v_start_341_);
lean_dec_ref(v_array_340_);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v_b_332_);
return v___x_347_;
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_array_fget_borrowed(v_array_340_, v_start_341_);
lean_inc(v___x_348_);
v___x_349_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_b_332_, v___x_348_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_349_, 1);
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_nat_add(v_start_341_, v___x_351_);
lean_dec(v_start_341_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v___x_352_);
v___x_354_ = v___x_344_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_array_340_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_stop_342_);
v___x_354_ = v_reuseFailAlloc_356_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
v_a_331_ = v___x_354_;
v_b_332_ = v_a_350_;
goto _start;
}
}
else
{
lean_del_object(v___x_344_);
lean_dec(v_stop_342_);
lean_dec(v_start_341_);
lean_dec_ref(v_array_340_);
return v___x_349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg___boxed(lean_object* v_a_358_, lean_object* v_b_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_358_, v_b_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_367_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1));
v___x_372_ = l_Lean_MessageData_ofFormat(v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(lean_object* v_sats_373_, lean_object* v_unusedHypotheses_374_, lean_object* v___x_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; size_t v_sz_386_; size_t v___x_387_; lean_object* v___x_388_; 
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_sats_373_);
lean_ctor_set(v___x_385_, 1, v_unusedHypotheses_374_);
v_sz_386_ = lean_array_size(v___y_376_);
v___x_387_ = ((size_t)0ULL);
v___x_388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v___y_376_, v_sz_386_, v___x_387_, v___x_385_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v_fst_390_; lean_object* v_snd_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
v_fst_390_ = lean_ctor_get(v_a_389_, 0);
lean_inc(v_fst_390_);
v_snd_391_ = lean_ctor_get(v_a_389_, 1);
lean_inc(v_snd_391_);
lean_dec(v_a_389_);
v___x_392_ = lean_array_get_size(v_fst_390_);
v___x_393_ = lean_nat_dec_eq(v___x_392_, v___x_375_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_394_ = lean_array_fget(v_fst_390_, v___x_375_);
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = l_Array_toSubarray___redArg(v_fst_390_, v___x_395_, v___x_392_);
v___x_397_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v___x_396_, v___x_394_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_410_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_410_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_410_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_410_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_bvExpr_402_; lean_object* v_expr_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v_bvExpr_402_ = lean_ctor_get(v_a_398_, 0);
v_expr_403_ = lean_ctor_get(v_a_398_, 2);
lean_inc_ref(v_expr_403_);
lean_inc_ref(v_bvExpr_402_);
v___x_404_ = l_Lean_ShareCommon_shareCommon___redArg(v_bvExpr_402_);
v___x_405_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed), 11, 1);
lean_closure_set(v___x_405_, 0, v_a_398_);
v___x_406_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
lean_ctor_set(v___x_406_, 2, v_snd_391_);
lean_ctor_set(v___x_406_, 3, v_expr_403_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_406_);
v___x_408_ = v___x_400_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_snd_391_);
v_a_411_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_397_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_397_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v_snd_391_);
lean_dec(v_fst_390_);
v___x_419_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2);
v___x_420_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v___x_419_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
return v___x_420_;
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v_a_421_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_388_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_388_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed(lean_object* v_sats_429_, lean_object* v_unusedHypotheses_430_, lean_object* v___x_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(v_sats_429_, v_unusedHypotheses_430_, v___x_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___x_431_);
return v_res_441_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_box(0);
v___x_443_ = lean_unsigned_to_nat(16u);
v___x_444_ = lean_mk_array(v___x_443_, v___x_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_unusedHypotheses_447_; 
v___x_445_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0);
v___x_446_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_unusedHypotheses_447_, 0, v___x_446_);
lean_ctor_set(v_unusedHypotheses_447_, 1, v___x_445_);
return v_unusedHypotheses_447_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2(void){
_start:
{
lean_object* v___x_448_; lean_object* v_unusedHypotheses_449_; lean_object* v_sats_450_; lean_object* v___f_451_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_449_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1);
v_sats_450_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___closed__1));
v___f_451_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed), 12, 3);
lean_closure_set(v___f_451_, 0, v_sats_450_);
lean_closure_set(v___f_451_, 1, v_unusedHypotheses_449_);
lean_closure_set(v___f_451_, 2, v___x_448_);
return v___f_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV(lean_object* v_g_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___f_462_; lean_object* v___x_463_; 
v___f_462_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2);
v___x_463_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_g_452_, v___f_462_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___boxed(lean_object* v_g_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0(lean_object* v_00_u03b2_475_, lean_object* v_m_476_, lean_object* v_a_477_, lean_object* v_b_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_m_476_, v_a_477_, v_b_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(lean_object* v_inst_480_, lean_object* v_R_481_, lean_object* v_a_482_, lean_object* v_b_483_, lean_object* v_c_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___redArg(v_a_482_, v_b_483_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___boxed(lean_object* v_inst_495_, lean_object* v_R_496_, lean_object* v_a_497_, lean_object* v_b_498_, lean_object* v_c_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(v_inst_495_, v_R_496_, v_a_497_, v_b_498_, v_c_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(lean_object* v_00_u03b1_510_, lean_object* v_msg_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_msg_511_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___boxed(lean_object* v_00_u03b1_522_, lean_object* v_msg_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(v_00_u03b1_522_, v_msg_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_533_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(lean_object* v_00_u03b2_534_, lean_object* v_a_535_, lean_object* v_x_536_){
_start:
{
uint8_t v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_a_535_, v_x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___boxed(lean_object* v_00_u03b2_538_, lean_object* v_a_539_, lean_object* v_x_540_){
_start:
{
uint8_t v_res_541_; lean_object* v_r_542_; 
v_res_541_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(v_00_u03b2_538_, v_a_539_, v_x_540_);
lean_dec(v_x_540_);
lean_dec_ref(v_a_539_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1(lean_object* v_00_u03b2_543_, lean_object* v_data_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1___redArg(v_data_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_546_, lean_object* v_i_547_, lean_object* v_source_548_, lean_object* v_target_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3___redArg(v_i_547_, v_source_548_, v_target_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__1_spec__3_spec__8___redArg(v_x_552_, v_x_553_);
return v___x_554_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_unsigned_to_nat(32u);
v___x_556_ = lean_mk_empty_array_with_capacity(v___x_555_);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1(void){
_start:
{
size_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_558_ = ((size_t)5ULL);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_unsigned_to_nat(32u);
v___x_561_ = lean_mk_empty_array_with_capacity(v___x_560_);
v___x_562_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__0);
v___x_563_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v___x_561_);
lean_ctor_set(v___x_563_, 2, v___x_559_);
lean_ctor_set(v___x_563_, 3, v___x_559_);
lean_ctor_set_usize(v___x_563_, 4, v___x_558_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; lean_object* v_traceState_567_; lean_object* v_traces_568_; lean_object* v___x_569_; lean_object* v_traceState_570_; lean_object* v_env_571_; lean_object* v_nextMacroScope_572_; lean_object* v_ngen_573_; lean_object* v_auxDeclNGen_574_; lean_object* v_cache_575_; lean_object* v_messages_576_; lean_object* v_infoState_577_; lean_object* v_snapshotTasks_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_597_; 
v___x_566_ = lean_st_ref_get(v___y_564_);
v_traceState_567_ = lean_ctor_get(v___x_566_, 4);
lean_inc_ref(v_traceState_567_);
lean_dec(v___x_566_);
v_traces_568_ = lean_ctor_get(v_traceState_567_, 0);
lean_inc_ref(v_traces_568_);
lean_dec_ref(v_traceState_567_);
v___x_569_ = lean_st_ref_take(v___y_564_);
v_traceState_570_ = lean_ctor_get(v___x_569_, 4);
v_env_571_ = lean_ctor_get(v___x_569_, 0);
v_nextMacroScope_572_ = lean_ctor_get(v___x_569_, 1);
v_ngen_573_ = lean_ctor_get(v___x_569_, 2);
v_auxDeclNGen_574_ = lean_ctor_get(v___x_569_, 3);
v_cache_575_ = lean_ctor_get(v___x_569_, 5);
v_messages_576_ = lean_ctor_get(v___x_569_, 6);
v_infoState_577_ = lean_ctor_get(v___x_569_, 7);
v_snapshotTasks_578_ = lean_ctor_get(v___x_569_, 8);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_597_ == 0)
{
v___x_580_ = v___x_569_;
v_isShared_581_ = v_isSharedCheck_597_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_snapshotTasks_578_);
lean_inc(v_infoState_577_);
lean_inc(v_messages_576_);
lean_inc(v_cache_575_);
lean_inc(v_traceState_570_);
lean_inc(v_auxDeclNGen_574_);
lean_inc(v_ngen_573_);
lean_inc(v_nextMacroScope_572_);
lean_inc(v_env_571_);
lean_dec(v___x_569_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_597_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
uint64_t v_tid_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_595_; 
v_tid_582_ = lean_ctor_get_uint64(v_traceState_570_, sizeof(void*)*1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_traceState_570_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v_traceState_570_, 0);
lean_dec(v_unused_596_);
v___x_584_ = v_traceState_570_;
v_isShared_585_ = v_isSharedCheck_595_;
goto v_resetjp_583_;
}
else
{
lean_dec(v_traceState_570_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_595_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___closed__1);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_586_);
v___x_588_ = v___x_584_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_586_);
lean_ctor_set_uint64(v_reuseFailAlloc_594_, sizeof(void*)*1, v_tid_582_);
v___x_588_ = v_reuseFailAlloc_594_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_590_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 4, v___x_588_);
v___x_590_ = v___x_580_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_env_571_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_nextMacroScope_572_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_ngen_573_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_auxDeclNGen_574_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_593_, 5, v_cache_575_);
lean_ctor_set(v_reuseFailAlloc_593_, 6, v_messages_576_);
lean_ctor_set(v_reuseFailAlloc_593_, 7, v_infoState_577_);
lean_ctor_set(v_reuseFailAlloc_593_, 8, v_snapshotTasks_578_);
v___x_590_ = v_reuseFailAlloc_593_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_st_ref_put(v___y_564_, v___x_590_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v_traces_568_);
return v___x_592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg___boxed(lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(v___y_598_);
lean_dec(v___y_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(v___y_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___boxed(lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_620_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(lean_object* v_opts_621_, lean_object* v_opt_622_){
_start:
{
lean_object* v_name_623_; lean_object* v_defValue_624_; lean_object* v_map_625_; lean_object* v___x_626_; 
v_name_623_ = lean_ctor_get(v_opt_622_, 0);
v_defValue_624_ = lean_ctor_get(v_opt_622_, 1);
v_map_625_ = lean_ctor_get(v_opts_621_, 0);
v___x_626_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_625_, v_name_623_);
if (lean_obj_tag(v___x_626_) == 0)
{
uint8_t v___x_627_; 
v___x_627_ = lean_unbox(v_defValue_624_);
return v___x_627_;
}
else
{
lean_object* v_val_628_; 
v_val_628_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_val_628_);
lean_dec_ref_known(v___x_626_, 1);
if (lean_obj_tag(v_val_628_) == 1)
{
uint8_t v_v_629_; 
v_v_629_ = lean_ctor_get_uint8(v_val_628_, 0);
lean_dec_ref_known(v_val_628_, 0);
return v_v_629_;
}
else
{
uint8_t v___x_630_; 
lean_dec(v_val_628_);
v___x_630_ = lean_unbox(v_defValue_624_);
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___boxed(lean_object* v_opts_631_, lean_object* v_opt_632_){
_start:
{
uint8_t v_res_633_; lean_object* v_r_634_; 
v_res_633_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_opts_631_, v_opt_632_);
lean_dec_ref(v_opt_632_);
lean_dec_ref(v_opts_631_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1));
v___x_639_ = l_Lean_MessageData_ofFormat(v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(lean_object* v_x_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed(lean_object* v_x_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(v_x_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec_ref(v_x_652_);
return v_res_662_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14(lean_object* v_e_663_){
_start:
{
if (lean_obj_tag(v_e_663_) == 0)
{
uint8_t v___x_664_; 
v___x_664_ = 2;
return v___x_664_;
}
else
{
uint8_t v___x_665_; 
v___x_665_ = 0;
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14___boxed(lean_object* v_e_666_){
_start:
{
uint8_t v_res_667_; lean_object* v_r_668_; 
v_res_667_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14(v_e_666_);
lean_dec_ref(v_e_666_);
v_r_668_ = lean_box(v_res_667_);
return v_r_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(lean_object* v_opts_669_, lean_object* v_opt_670_){
_start:
{
lean_object* v_name_671_; lean_object* v_defValue_672_; lean_object* v_map_673_; lean_object* v___x_674_; 
v_name_671_ = lean_ctor_get(v_opt_670_, 0);
v_defValue_672_ = lean_ctor_get(v_opt_670_, 1);
v_map_673_ = lean_ctor_get(v_opts_669_, 0);
v___x_674_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_673_, v_name_671_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_inc(v_defValue_672_);
return v_defValue_672_;
}
else
{
lean_object* v_val_675_; 
v_val_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_val_675_);
lean_dec_ref_known(v___x_674_, 1);
if (lean_obj_tag(v_val_675_) == 3)
{
lean_object* v_v_676_; 
v_v_676_ = lean_ctor_get(v_val_675_, 0);
lean_inc(v_v_676_);
lean_dec_ref_known(v_val_675_, 1);
return v_v_676_;
}
else
{
lean_dec(v_val_675_);
lean_inc(v_defValue_672_);
return v_defValue_672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15___boxed(lean_object* v_opts_677_, lean_object* v_opt_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(v_opts_677_, v_opt_678_);
lean_dec_ref(v_opt_678_);
lean_dec_ref(v_opts_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17(size_t v_sz_680_, size_t v_i_681_, lean_object* v_bs_682_){
_start:
{
uint8_t v___x_683_; 
v___x_683_ = lean_usize_dec_lt(v_i_681_, v_sz_680_);
if (v___x_683_ == 0)
{
return v_bs_682_;
}
else
{
lean_object* v_v_684_; lean_object* v_msg_685_; lean_object* v___x_686_; lean_object* v_bs_x27_687_; size_t v___x_688_; size_t v___x_689_; lean_object* v___x_690_; 
v_v_684_ = lean_array_uget_borrowed(v_bs_682_, v_i_681_);
v_msg_685_ = lean_ctor_get(v_v_684_, 1);
lean_inc_ref(v_msg_685_);
v___x_686_ = lean_unsigned_to_nat(0u);
v_bs_x27_687_ = lean_array_uset(v_bs_682_, v_i_681_, v___x_686_);
v___x_688_ = ((size_t)1ULL);
v___x_689_ = lean_usize_add(v_i_681_, v___x_688_);
v___x_690_ = lean_array_uset(v_bs_x27_687_, v_i_681_, v_msg_685_);
v_i_681_ = v___x_689_;
v_bs_682_ = v___x_690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17___boxed(lean_object* v_sz_692_, lean_object* v_i_693_, lean_object* v_bs_694_){
_start:
{
size_t v_sz_boxed_695_; size_t v_i_boxed_696_; lean_object* v_res_697_; 
v_sz_boxed_695_ = lean_unbox_usize(v_sz_692_);
lean_dec(v_sz_692_);
v_i_boxed_696_ = lean_unbox_usize(v_i_693_);
lean_dec(v_i_693_);
v_res_697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17(v_sz_boxed_695_, v_i_boxed_696_, v_bs_694_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg(lean_object* v_oldTraces_698_, lean_object* v_data_699_, lean_object* v_ref_700_, lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_toCold_707_; lean_object* v_currRecDepth_708_; lean_object* v_ref_709_; uint8_t v_diag_710_; uint8_t v_suppressElabErrors_711_; lean_object* v___x_712_; lean_object* v_traceState_713_; lean_object* v_traces_714_; lean_object* v_ref_715_; lean_object* v___x_716_; lean_object* v___x_717_; size_t v_sz_718_; size_t v___x_719_; lean_object* v___x_720_; lean_object* v_msg_721_; lean_object* v___x_722_; lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_760_; 
v_toCold_707_ = lean_ctor_get(v___y_704_, 0);
v_currRecDepth_708_ = lean_ctor_get(v___y_704_, 1);
v_ref_709_ = lean_ctor_get(v___y_704_, 2);
v_diag_710_ = lean_ctor_get_uint8(v___y_704_, sizeof(void*)*3);
v_suppressElabErrors_711_ = lean_ctor_get_uint8(v___y_704_, sizeof(void*)*3 + 1);
v___x_712_ = lean_st_ref_get(v___y_705_);
v_traceState_713_ = lean_ctor_get(v___x_712_, 4);
lean_inc_ref(v_traceState_713_);
lean_dec(v___x_712_);
v_traces_714_ = lean_ctor_get(v_traceState_713_, 0);
lean_inc_ref(v_traces_714_);
lean_dec_ref(v_traceState_713_);
v_ref_715_ = l_Lean_replaceRef(v_ref_700_, v_ref_709_);
lean_inc(v_currRecDepth_708_);
lean_inc_ref(v_toCold_707_);
v___x_716_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_716_, 0, v_toCold_707_);
lean_ctor_set(v___x_716_, 1, v_currRecDepth_708_);
lean_ctor_set(v___x_716_, 2, v_ref_715_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*3, v_diag_710_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*3 + 1, v_suppressElabErrors_711_);
v___x_717_ = l_Lean_PersistentArray_toArray___redArg(v_traces_714_);
lean_dec_ref(v_traces_714_);
v_sz_718_ = lean_array_size(v___x_717_);
v___x_719_ = ((size_t)0ULL);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12_spec__17(v_sz_718_, v___x_719_, v___x_717_);
v_msg_721_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_721_, 0, v_data_699_);
lean_ctor_set(v_msg_721_, 1, v_msg_701_);
lean_ctor_set(v_msg_721_, 2, v___x_720_);
v___x_722_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_721_, v___y_702_, v___y_703_, v___x_716_, v___y_705_);
lean_dec_ref_known(v___x_716_, 3);
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_760_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_760_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_760_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v_traceState_728_; lean_object* v_env_729_; lean_object* v_nextMacroScope_730_; lean_object* v_ngen_731_; lean_object* v_auxDeclNGen_732_; lean_object* v_cache_733_; lean_object* v_messages_734_; lean_object* v_infoState_735_; lean_object* v_snapshotTasks_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_759_; 
v___x_727_ = lean_st_ref_take(v___y_705_);
v_traceState_728_ = lean_ctor_get(v___x_727_, 4);
v_env_729_ = lean_ctor_get(v___x_727_, 0);
v_nextMacroScope_730_ = lean_ctor_get(v___x_727_, 1);
v_ngen_731_ = lean_ctor_get(v___x_727_, 2);
v_auxDeclNGen_732_ = lean_ctor_get(v___x_727_, 3);
v_cache_733_ = lean_ctor_get(v___x_727_, 5);
v_messages_734_ = lean_ctor_get(v___x_727_, 6);
v_infoState_735_ = lean_ctor_get(v___x_727_, 7);
v_snapshotTasks_736_ = lean_ctor_get(v___x_727_, 8);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_759_ == 0)
{
v___x_738_ = v___x_727_;
v_isShared_739_ = v_isSharedCheck_759_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_snapshotTasks_736_);
lean_inc(v_infoState_735_);
lean_inc(v_messages_734_);
lean_inc(v_cache_733_);
lean_inc(v_traceState_728_);
lean_inc(v_auxDeclNGen_732_);
lean_inc(v_ngen_731_);
lean_inc(v_nextMacroScope_730_);
lean_inc(v_env_729_);
lean_dec(v___x_727_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_759_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
uint64_t v_tid_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_757_; 
v_tid_740_ = lean_ctor_get_uint64(v_traceState_728_, sizeof(void*)*1);
v_isSharedCheck_757_ = !lean_is_exclusive(v_traceState_728_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v_traceState_728_, 0);
lean_dec(v_unused_758_);
v___x_742_ = v_traceState_728_;
v_isShared_743_ = v_isSharedCheck_757_;
goto v_resetjp_741_;
}
else
{
lean_dec(v_traceState_728_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_757_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v_ref_700_);
lean_ctor_set(v___x_744_, 1, v_a_723_);
v___x_745_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_698_, v___x_744_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_745_);
v___x_747_ = v___x_742_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_745_);
lean_ctor_set_uint64(v_reuseFailAlloc_756_, sizeof(void*)*1, v_tid_740_);
v___x_747_ = v_reuseFailAlloc_756_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_749_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v___x_747_);
v___x_749_ = v___x_738_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_env_729_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_nextMacroScope_730_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_ngen_731_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v_auxDeclNGen_732_);
lean_ctor_set(v_reuseFailAlloc_755_, 4, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_755_, 5, v_cache_733_);
lean_ctor_set(v_reuseFailAlloc_755_, 6, v_messages_734_);
lean_ctor_set(v_reuseFailAlloc_755_, 7, v_infoState_735_);
lean_ctor_set(v_reuseFailAlloc_755_, 8, v_snapshotTasks_736_);
v___x_749_ = v_reuseFailAlloc_755_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_750_ = lean_st_ref_put(v___y_705_, v___x_749_);
v___x_751_ = lean_box(0);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_751_);
v___x_753_ = v___x_725_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg___boxed(lean_object* v_oldTraces_761_, lean_object* v_data_762_, lean_object* v_ref_763_, lean_object* v_msg_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg(v_oldTraces_761_, v_data_762_, v_ref_763_, v_msg_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(lean_object* v_x_771_){
_start:
{
if (lean_obj_tag(v_x_771_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
v_a_773_ = lean_ctor_get(v_x_771_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v_x_771_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v_x_771_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v_x_771_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set_tag(v___x_775_, 1);
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
v_a_781_ = lean_ctor_get(v_x_771_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_x_771_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v_x_771_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v_x_771_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set_tag(v___x_783_, 0);
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg___boxed(lean_object* v_x_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_x_789_);
return v_res_791_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0(void){
_start:
{
lean_object* v___x_792_; double v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_float_of_nat(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__1));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3(void){
_start:
{
lean_object* v___x_797_; double v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(1000u);
v___x_798_ = lean_float_of_nat(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(lean_object* v_cls_799_, uint8_t v_collapsed_800_, lean_object* v_tag_801_, lean_object* v_opts_802_, uint8_t v_clsEnabled_803_, lean_object* v_oldTraces_804_, lean_object* v_msg_805_, lean_object* v_resStartStop_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_fst_816_; lean_object* v_snd_817_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v_data_821_; lean_object* v_fst_832_; lean_object* v_snd_833_; lean_object* v___x_834_; uint8_t v___x_835_; lean_object* v___y_837_; lean_object* v_a_838_; uint8_t v___y_853_; double v___y_884_; 
v_fst_816_ = lean_ctor_get(v_resStartStop_806_, 0);
lean_inc(v_fst_816_);
v_snd_817_ = lean_ctor_get(v_resStartStop_806_, 1);
lean_inc(v_snd_817_);
lean_dec_ref(v_resStartStop_806_);
v_fst_832_ = lean_ctor_get(v_snd_817_, 0);
lean_inc(v_fst_832_);
v_snd_833_ = lean_ctor_get(v_snd_817_, 1);
lean_inc(v_snd_833_);
lean_dec(v_snd_817_);
v___x_834_ = l_Lean_trace_profiler;
v___x_835_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_opts_802_, v___x_834_);
if (v___x_835_ == 0)
{
v___y_853_ = v___x_835_;
goto v___jp_852_;
}
else
{
lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_889_ = l_Lean_trace_profiler_useHeartbeats;
v___x_890_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_opts_802_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; double v___x_893_; double v___x_894_; double v___x_895_; 
v___x_891_ = l_Lean_trace_profiler_threshold;
v___x_892_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(v_opts_802_, v___x_891_);
v___x_893_ = lean_float_of_nat(v___x_892_);
v___x_894_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__3);
v___x_895_ = lean_float_div(v___x_893_, v___x_894_);
v___y_884_ = v___x_895_;
goto v___jp_883_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; double v___x_898_; 
v___x_896_ = l_Lean_trace_profiler_threshold;
v___x_897_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__15(v_opts_802_, v___x_896_);
v___x_898_ = lean_float_of_nat(v___x_897_);
v___y_884_ = v___x_898_;
goto v___jp_883_;
}
}
v___jp_818_:
{
lean_object* v___x_822_; 
lean_inc(v___y_820_);
v___x_822_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg(v_oldTraces_804_, v_data_821_, v___y_820_, v___y_819_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v___x_823_; 
lean_dec_ref_known(v___x_822_, 1);
v___x_823_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_fst_816_);
return v___x_823_;
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec(v_fst_816_);
v_a_824_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_822_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_822_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
v___jp_836_:
{
uint8_t v_result_839_; lean_object* v___x_840_; lean_object* v___x_841_; double v___x_842_; lean_object* v_data_843_; 
v_result_839_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__14(v_fst_816_);
v___x_840_ = lean_box(v_result_839_);
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
v___x_842_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0);
lean_inc_ref(v_tag_801_);
lean_inc_ref(v___x_841_);
lean_inc(v_cls_799_);
v_data_843_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_843_, 0, v_cls_799_);
lean_ctor_set(v_data_843_, 1, v___x_841_);
lean_ctor_set(v_data_843_, 2, v_tag_801_);
lean_ctor_set_float(v_data_843_, sizeof(void*)*3, v___x_842_);
lean_ctor_set_float(v_data_843_, sizeof(void*)*3 + 8, v___x_842_);
lean_ctor_set_uint8(v_data_843_, sizeof(void*)*3 + 16, v_collapsed_800_);
if (v___x_835_ == 0)
{
lean_dec_ref_known(v___x_841_, 1);
lean_dec(v_snd_833_);
lean_dec(v_fst_832_);
lean_dec_ref(v_tag_801_);
lean_dec(v_cls_799_);
v___y_819_ = v_a_838_;
v___y_820_ = v___y_837_;
v_data_821_ = v_data_843_;
goto v___jp_818_;
}
else
{
lean_object* v_data_844_; double v___x_845_; double v___x_846_; 
lean_dec_ref_known(v_data_843_, 3);
v_data_844_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_844_, 0, v_cls_799_);
lean_ctor_set(v_data_844_, 1, v___x_841_);
lean_ctor_set(v_data_844_, 2, v_tag_801_);
v___x_845_ = lean_unbox_float(v_fst_832_);
lean_dec(v_fst_832_);
lean_ctor_set_float(v_data_844_, sizeof(void*)*3, v___x_845_);
v___x_846_ = lean_unbox_float(v_snd_833_);
lean_dec(v_snd_833_);
lean_ctor_set_float(v_data_844_, sizeof(void*)*3 + 8, v___x_846_);
lean_ctor_set_uint8(v_data_844_, sizeof(void*)*3 + 16, v_collapsed_800_);
v___y_819_ = v_a_838_;
v___y_820_ = v___y_837_;
v_data_821_ = v_data_844_;
goto v___jp_818_;
}
}
v___jp_847_:
{
lean_object* v_ref_848_; lean_object* v___x_849_; 
v_ref_848_ = lean_ctor_get(v___y_813_, 2);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
lean_inc(v_fst_816_);
v___x_849_ = lean_apply_10(v_msg_805_, v_fst_816_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, lean_box(0));
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
v___y_837_ = v_ref_848_;
v_a_838_ = v_a_850_;
goto v___jp_836_;
}
else
{
lean_object* v___x_851_; 
lean_dec_ref_known(v___x_849_, 1);
v___x_851_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__2);
v___y_837_ = v_ref_848_;
v_a_838_ = v___x_851_;
goto v___jp_836_;
}
}
v___jp_852_:
{
if (v_clsEnabled_803_ == 0)
{
if (v___y_853_ == 0)
{
lean_object* v___x_854_; lean_object* v_traceState_855_; lean_object* v_env_856_; lean_object* v_nextMacroScope_857_; lean_object* v_ngen_858_; lean_object* v_auxDeclNGen_859_; lean_object* v_cache_860_; lean_object* v_messages_861_; lean_object* v_infoState_862_; lean_object* v_snapshotTasks_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_snd_833_);
lean_dec(v_fst_832_);
lean_dec_ref(v_msg_805_);
lean_dec_ref(v_tag_801_);
lean_dec(v_cls_799_);
v___x_854_ = lean_st_ref_take(v___y_814_);
v_traceState_855_ = lean_ctor_get(v___x_854_, 4);
v_env_856_ = lean_ctor_get(v___x_854_, 0);
v_nextMacroScope_857_ = lean_ctor_get(v___x_854_, 1);
v_ngen_858_ = lean_ctor_get(v___x_854_, 2);
v_auxDeclNGen_859_ = lean_ctor_get(v___x_854_, 3);
v_cache_860_ = lean_ctor_get(v___x_854_, 5);
v_messages_861_ = lean_ctor_get(v___x_854_, 6);
v_infoState_862_ = lean_ctor_get(v___x_854_, 7);
v_snapshotTasks_863_ = lean_ctor_get(v___x_854_, 8);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_882_ == 0)
{
v___x_865_ = v___x_854_;
v_isShared_866_ = v_isSharedCheck_882_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_snapshotTasks_863_);
lean_inc(v_infoState_862_);
lean_inc(v_messages_861_);
lean_inc(v_cache_860_);
lean_inc(v_traceState_855_);
lean_inc(v_auxDeclNGen_859_);
lean_inc(v_ngen_858_);
lean_inc(v_nextMacroScope_857_);
lean_inc(v_env_856_);
lean_dec(v___x_854_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_882_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
uint64_t v_tid_867_; lean_object* v_traces_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_881_; 
v_tid_867_ = lean_ctor_get_uint64(v_traceState_855_, sizeof(void*)*1);
v_traces_868_ = lean_ctor_get(v_traceState_855_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v_traceState_855_);
if (v_isSharedCheck_881_ == 0)
{
v___x_870_ = v_traceState_855_;
v_isShared_871_ = v_isSharedCheck_881_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_traces_868_);
lean_dec(v_traceState_855_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_881_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_804_, v_traces_868_);
lean_dec_ref(v_traces_868_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_872_);
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_872_);
lean_ctor_set_uint64(v_reuseFailAlloc_880_, sizeof(void*)*1, v_tid_867_);
v___x_874_ = v_reuseFailAlloc_880_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_876_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 4, v___x_874_);
v___x_876_ = v___x_865_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_env_856_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_nextMacroScope_857_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_ngen_858_);
lean_ctor_set(v_reuseFailAlloc_879_, 3, v_auxDeclNGen_859_);
lean_ctor_set(v_reuseFailAlloc_879_, 4, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_879_, 5, v_cache_860_);
lean_ctor_set(v_reuseFailAlloc_879_, 6, v_messages_861_);
lean_ctor_set(v_reuseFailAlloc_879_, 7, v_infoState_862_);
lean_ctor_set(v_reuseFailAlloc_879_, 8, v_snapshotTasks_863_);
v___x_876_ = v_reuseFailAlloc_879_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_st_ref_put(v___y_814_, v___x_876_);
v___x_878_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_fst_816_);
return v___x_878_;
}
}
}
}
}
else
{
goto v___jp_847_;
}
}
else
{
goto v___jp_847_;
}
}
v___jp_883_:
{
double v___x_885_; double v___x_886_; double v___x_887_; uint8_t v___x_888_; 
v___x_885_ = lean_unbox_float(v_snd_833_);
v___x_886_ = lean_unbox_float(v_fst_832_);
v___x_887_ = lean_float_sub(v___x_885_, v___x_886_);
v___x_888_ = lean_float_decLt(v___y_884_, v___x_887_);
v___y_853_ = v___x_888_;
goto v___jp_852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___boxed(lean_object** _args){
lean_object* v_cls_899_ = _args[0];
lean_object* v_collapsed_900_ = _args[1];
lean_object* v_tag_901_ = _args[2];
lean_object* v_opts_902_ = _args[3];
lean_object* v_clsEnabled_903_ = _args[4];
lean_object* v_oldTraces_904_ = _args[5];
lean_object* v_msg_905_ = _args[6];
lean_object* v_resStartStop_906_ = _args[7];
lean_object* v___y_907_ = _args[8];
lean_object* v___y_908_ = _args[9];
lean_object* v___y_909_ = _args[10];
lean_object* v___y_910_ = _args[11];
lean_object* v___y_911_ = _args[12];
lean_object* v___y_912_ = _args[13];
lean_object* v___y_913_ = _args[14];
lean_object* v___y_914_ = _args[15];
lean_object* v___y_915_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_916_; uint8_t v_clsEnabled_boxed_917_; lean_object* v_res_918_; 
v_collapsed_boxed_916_ = lean_unbox(v_collapsed_900_);
v_clsEnabled_boxed_917_ = lean_unbox(v_clsEnabled_903_);
v_res_918_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(v_cls_899_, v_collapsed_boxed_916_, v_tag_901_, v_opts_902_, v_clsEnabled_boxed_917_, v_oldTraces_904_, v_msg_905_, v_resStartStop_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec_ref(v_opts_902_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
lean_inc(v_x_919_);
return v_x_919_;
}
else
{
lean_object* v_key_921_; lean_object* v_value_922_; lean_object* v_tail_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_key_921_ = lean_ctor_get(v_x_920_, 0);
v_value_922_ = lean_ctor_get(v_x_920_, 1);
v_tail_923_ = lean_ctor_get(v_x_920_, 2);
v___x_924_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_x_919_, v_tail_923_);
lean_inc(v_value_922_);
lean_inc(v_key_921_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v_key_921_);
lean_ctor_set(v___x_925_, 1, v_value_922_);
v___x_926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_924_);
return v___x_926_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___boxed(lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_x_927_, v_x_928_);
lean_dec(v_x_928_);
lean_dec(v_x_927_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(lean_object* v_as_930_, size_t v_i_931_, size_t v_stop_932_, lean_object* v_b_933_){
_start:
{
uint8_t v___x_934_; 
v___x_934_ = lean_usize_dec_eq(v_i_931_, v_stop_932_);
if (v___x_934_ == 0)
{
size_t v___x_935_; size_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_sub(v_i_931_, v___x_935_);
v___x_937_ = lean_array_uget_borrowed(v_as_930_, v___x_936_);
v___x_938_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_b_933_, v___x_937_);
lean_dec(v_b_933_);
v_i_931_ = v___x_936_;
v_b_933_ = v___x_938_;
goto _start;
}
else
{
return v_b_933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___boxed(lean_object* v_as_940_, lean_object* v_i_941_, lean_object* v_stop_942_, lean_object* v_b_943_){
_start:
{
size_t v_i_boxed_944_; size_t v_stop_boxed_945_; lean_object* v_res_946_; 
v_i_boxed_944_ = lean_unbox_usize(v_i_941_);
lean_dec(v_i_941_);
v_stop_boxed_945_ = lean_unbox_usize(v_stop_942_);
lean_dec(v_stop_942_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_as_940_, v_i_boxed_944_, v_stop_boxed_945_, v_b_943_);
lean_dec_ref(v_as_940_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(lean_object* v_x_954_){
_start:
{
switch(lean_obj_tag(v_x_954_))
{
case 0:
{
lean_object* v_a_955_; lean_object* v___x_956_; 
v_a_955_ = lean_ctor_get(v_x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v_x_954_, 1);
v___x_956_ = l_Std_Tactic_BVDecide_BVPred_toString(v_a_955_);
return v___x_956_;
}
case 1:
{
uint8_t v_a_957_; 
v_a_957_ = lean_ctor_get_uint8(v_x_954_, 0);
lean_dec_ref_known(v_x_954_, 0);
if (v_a_957_ == 0)
{
lean_object* v___x_958_; 
v___x_958_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__0));
return v___x_958_;
}
else
{
lean_object* v___x_959_; 
v___x_959_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__1));
return v___x_959_;
}
}
case 2:
{
lean_object* v_a_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_a_960_ = lean_ctor_get(v_x_954_, 0);
lean_inc_ref(v_a_960_);
lean_dec_ref_known(v_x_954_, 1);
v___x_961_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__2));
v___x_962_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_960_);
v___x_963_ = lean_string_append(v___x_961_, v___x_962_);
lean_dec_ref(v___x_962_);
return v___x_963_;
}
case 3:
{
uint8_t v_a_964_; lean_object* v_a_965_; lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_a_964_ = lean_ctor_get_uint8(v_x_954_, sizeof(void*)*2);
v_a_965_ = lean_ctor_get(v_x_954_, 0);
lean_inc_ref(v_a_965_);
v_a_966_ = lean_ctor_get(v_x_954_, 1);
lean_inc_ref(v_a_966_);
lean_dec_ref_known(v_x_954_, 2);
v___x_967_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__3));
v___x_968_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_965_);
v___x_969_ = lean_string_append(v___x_967_, v___x_968_);
lean_dec_ref(v___x_968_);
v___x_970_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4));
v___x_971_ = lean_string_append(v___x_969_, v___x_970_);
v___x_972_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_964_);
v___x_973_ = lean_string_append(v___x_971_, v___x_972_);
lean_dec_ref(v___x_972_);
v___x_974_ = lean_string_append(v___x_973_, v___x_970_);
v___x_975_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_966_);
v___x_976_ = lean_string_append(v___x_974_, v___x_975_);
lean_dec_ref(v___x_975_);
v___x_977_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__5));
v___x_978_ = lean_string_append(v___x_976_, v___x_977_);
return v___x_978_;
}
default: 
{
lean_object* v_a_979_; lean_object* v_a_980_; lean_object* v_a_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_a_979_ = lean_ctor_get(v_x_954_, 0);
lean_inc_ref(v_a_979_);
v_a_980_ = lean_ctor_get(v_x_954_, 1);
lean_inc_ref(v_a_980_);
v_a_981_ = lean_ctor_get(v_x_954_, 2);
lean_inc_ref(v_a_981_);
lean_dec_ref_known(v_x_954_, 3);
v___x_982_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__6));
v___x_983_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_979_);
v___x_984_ = lean_string_append(v___x_982_, v___x_983_);
lean_dec_ref(v___x_983_);
v___x_985_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__4));
v___x_986_ = lean_string_append(v___x_984_, v___x_985_);
v___x_987_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_980_);
v___x_988_ = lean_string_append(v___x_986_, v___x_987_);
lean_dec_ref(v___x_987_);
v___x_989_ = lean_string_append(v___x_988_, v___x_985_);
v___x_990_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_a_981_);
v___x_991_ = lean_string_append(v___x_989_, v___x_990_);
lean_dec_ref(v___x_990_);
v___x_992_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___closed__5));
v___x_993_ = lean_string_append(v___x_991_, v___x_992_);
return v___x_993_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(lean_object* v_a_994_, lean_object* v_x_995_){
_start:
{
if (lean_obj_tag(v_x_995_) == 0)
{
uint8_t v___x_996_; 
v___x_996_ = 0;
return v___x_996_;
}
else
{
lean_object* v_key_997_; lean_object* v_tail_998_; uint8_t v___x_999_; 
v_key_997_ = lean_ctor_get(v_x_995_, 0);
v_tail_998_ = lean_ctor_get(v_x_995_, 2);
v___x_999_ = lean_nat_dec_eq(v_key_997_, v_a_994_);
if (v___x_999_ == 0)
{
v_x_995_ = v_tail_998_;
goto _start;
}
else
{
return v___x_999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_a_1001_, lean_object* v_x_1002_){
_start:
{
uint8_t v_res_1003_; lean_object* v_r_1004_; 
v_res_1003_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(v_a_1001_, v_x_1002_);
lean_dec(v_x_1002_);
lean_dec(v_a_1001_);
v_r_1004_ = lean_box(v_res_1003_);
return v_r_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(lean_object* v_a_1005_, lean_object* v_b_1006_, lean_object* v_x_1007_){
_start:
{
if (lean_obj_tag(v_x_1007_) == 0)
{
lean_dec(v_b_1006_);
lean_dec(v_a_1005_);
return v_x_1007_;
}
else
{
lean_object* v_key_1008_; lean_object* v_value_1009_; lean_object* v_tail_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1022_; 
v_key_1008_ = lean_ctor_get(v_x_1007_, 0);
v_value_1009_ = lean_ctor_get(v_x_1007_, 1);
v_tail_1010_ = lean_ctor_get(v_x_1007_, 2);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_x_1007_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1012_ = v_x_1007_;
v_isShared_1013_ = v_isSharedCheck_1022_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_tail_1010_);
lean_inc(v_value_1009_);
lean_inc(v_key_1008_);
lean_dec(v_x_1007_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1022_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
uint8_t v___x_1014_; 
v___x_1014_ = lean_nat_dec_eq(v_key_1008_, v_a_1005_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1015_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(v_a_1005_, v_b_1006_, v_tail_1010_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 2, v___x_1015_);
v___x_1017_ = v___x_1012_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_key_1008_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_value_1009_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
else
{
lean_object* v___x_1020_; 
lean_dec(v_value_1009_);
lean_dec(v_key_1008_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 1, v_b_1006_);
lean_ctor_set(v___x_1012_, 0, v_a_1005_);
v___x_1020_ = v___x_1012_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1005_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_b_1006_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_tail_1010_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19___redArg(lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
if (lean_obj_tag(v_x_1024_) == 0)
{
return v_x_1023_;
}
else
{
lean_object* v_key_1025_; lean_object* v_value_1026_; lean_object* v_tail_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1050_; 
v_key_1025_ = lean_ctor_get(v_x_1024_, 0);
v_value_1026_ = lean_ctor_get(v_x_1024_, 1);
v_tail_1027_ = lean_ctor_get(v_x_1024_, 2);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_x_1024_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1029_ = v_x_1024_;
v_isShared_1030_ = v_isSharedCheck_1050_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_tail_1027_);
lean_inc(v_value_1026_);
lean_inc(v_key_1025_);
lean_dec(v_x_1024_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1050_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; uint64_t v___x_1032_; uint64_t v___x_1033_; uint64_t v___x_1034_; uint64_t v_fold_1035_; uint64_t v___x_1036_; uint64_t v___x_1037_; uint64_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; size_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1031_ = lean_array_get_size(v_x_1023_);
v___x_1032_ = lean_uint64_of_nat(v_key_1025_);
v___x_1033_ = 32ULL;
v___x_1034_ = lean_uint64_shift_right(v___x_1032_, v___x_1033_);
v_fold_1035_ = lean_uint64_xor(v___x_1032_, v___x_1034_);
v___x_1036_ = 16ULL;
v___x_1037_ = lean_uint64_shift_right(v_fold_1035_, v___x_1036_);
v___x_1038_ = lean_uint64_xor(v_fold_1035_, v___x_1037_);
v___x_1039_ = lean_uint64_to_usize(v___x_1038_);
v___x_1040_ = lean_usize_of_nat(v___x_1031_);
v___x_1041_ = ((size_t)1ULL);
v___x_1042_ = lean_usize_sub(v___x_1040_, v___x_1041_);
v___x_1043_ = lean_usize_land(v___x_1039_, v___x_1042_);
v___x_1044_ = lean_array_uget_borrowed(v_x_1023_, v___x_1043_);
lean_inc(v___x_1044_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 2, v___x_1044_);
v___x_1046_ = v___x_1029_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_key_1025_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_value_1026_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_array_uset(v_x_1023_, v___x_1043_, v___x_1046_);
v_x_1023_ = v___x_1047_;
v_x_1024_ = v_tail_1027_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15___redArg(lean_object* v_i_1051_, lean_object* v_source_1052_, lean_object* v_target_1053_){
_start:
{
lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = lean_array_get_size(v_source_1052_);
v___x_1055_ = lean_nat_dec_lt(v_i_1051_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_dec_ref(v_source_1052_);
lean_dec(v_i_1051_);
return v_target_1053_;
}
else
{
lean_object* v_es_1056_; lean_object* v___x_1057_; lean_object* v_source_1058_; lean_object* v_target_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_es_1056_ = lean_array_fget(v_source_1052_, v_i_1051_);
v___x_1057_ = lean_box(0);
v_source_1058_ = lean_array_fset(v_source_1052_, v_i_1051_, v___x_1057_);
v_target_1059_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19___redArg(v_target_1053_, v_es_1056_);
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1061_ = lean_nat_add(v_i_1051_, v___x_1060_);
lean_dec(v_i_1051_);
v_i_1051_ = v___x_1061_;
v_source_1052_ = v_source_1058_;
v_target_1053_ = v_target_1059_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5___redArg(lean_object* v_data_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v_nbuckets_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1064_ = lean_array_get_size(v_data_1063_);
v___x_1065_ = lean_unsigned_to_nat(2u);
v_nbuckets_1066_ = lean_nat_mul(v___x_1064_, v___x_1065_);
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = lean_box(0);
v___x_1069_ = lean_mk_array(v_nbuckets_1066_, v___x_1068_);
v___x_1070_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15___redArg(v___x_1067_, v_data_1063_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1___redArg(lean_object* v_m_1071_, lean_object* v_a_1072_, lean_object* v_b_1073_){
_start:
{
lean_object* v_size_1074_; lean_object* v_buckets_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1118_; 
v_size_1074_ = lean_ctor_get(v_m_1071_, 0);
v_buckets_1075_ = lean_ctor_get(v_m_1071_, 1);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_m_1071_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1077_ = v_m_1071_;
v_isShared_1078_ = v_isSharedCheck_1118_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_buckets_1075_);
lean_inc(v_size_1074_);
lean_dec(v_m_1071_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1118_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; uint64_t v___x_1080_; uint64_t v___x_1081_; uint64_t v___x_1082_; uint64_t v_fold_1083_; uint64_t v___x_1084_; uint64_t v___x_1085_; uint64_t v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; size_t v___x_1090_; size_t v___x_1091_; lean_object* v_bkt_1092_; uint8_t v___x_1093_; 
v___x_1079_ = lean_array_get_size(v_buckets_1075_);
v___x_1080_ = lean_uint64_of_nat(v_a_1072_);
v___x_1081_ = 32ULL;
v___x_1082_ = lean_uint64_shift_right(v___x_1080_, v___x_1081_);
v_fold_1083_ = lean_uint64_xor(v___x_1080_, v___x_1082_);
v___x_1084_ = 16ULL;
v___x_1085_ = lean_uint64_shift_right(v_fold_1083_, v___x_1084_);
v___x_1086_ = lean_uint64_xor(v_fold_1083_, v___x_1085_);
v___x_1087_ = lean_uint64_to_usize(v___x_1086_);
v___x_1088_ = lean_usize_of_nat(v___x_1079_);
v___x_1089_ = ((size_t)1ULL);
v___x_1090_ = lean_usize_sub(v___x_1088_, v___x_1089_);
v___x_1091_ = lean_usize_land(v___x_1087_, v___x_1090_);
v_bkt_1092_ = lean_array_uget_borrowed(v_buckets_1075_, v___x_1091_);
v___x_1093_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(v_a_1072_, v_bkt_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v_size_x27_1095_; lean_object* v___x_1096_; lean_object* v_buckets_x27_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1094_ = lean_unsigned_to_nat(1u);
v_size_x27_1095_ = lean_nat_add(v_size_1074_, v___x_1094_);
lean_dec(v_size_1074_);
lean_inc(v_bkt_1092_);
v___x_1096_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1096_, 0, v_a_1072_);
lean_ctor_set(v___x_1096_, 1, v_b_1073_);
lean_ctor_set(v___x_1096_, 2, v_bkt_1092_);
v_buckets_x27_1097_ = lean_array_uset(v_buckets_1075_, v___x_1091_, v___x_1096_);
v___x_1098_ = lean_unsigned_to_nat(4u);
v___x_1099_ = lean_nat_mul(v_size_x27_1095_, v___x_1098_);
v___x_1100_ = lean_unsigned_to_nat(3u);
v___x_1101_ = lean_nat_div(v___x_1099_, v___x_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_array_get_size(v_buckets_x27_1097_);
v___x_1103_ = lean_nat_dec_le(v___x_1101_, v___x_1102_);
lean_dec(v___x_1101_);
if (v___x_1103_ == 0)
{
lean_object* v_val_1104_; lean_object* v___x_1106_; 
v_val_1104_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5___redArg(v_buckets_x27_1097_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v_val_1104_);
lean_ctor_set(v___x_1077_, 0, v_size_x27_1095_);
v___x_1106_ = v___x_1077_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_size_x27_1095_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_val_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v___x_1109_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v_buckets_x27_1097_);
lean_ctor_set(v___x_1077_, 0, v_size_x27_1095_);
v___x_1109_ = v___x_1077_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_size_x27_1095_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_buckets_x27_1097_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
else
{
lean_object* v___x_1111_; lean_object* v_buckets_x27_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
lean_inc(v_bkt_1092_);
v___x_1111_ = lean_box(0);
v_buckets_x27_1112_ = lean_array_uset(v_buckets_1075_, v___x_1091_, v___x_1111_);
v___x_1113_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(v_a_1072_, v_b_1073_, v_bkt_1092_);
v___x_1114_ = lean_array_uset(v_buckets_x27_1112_, v___x_1091_, v___x_1113_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1114_);
v___x_1116_ = v___x_1077_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_size_1074_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(lean_object* v_as_x27_1119_, lean_object* v_b_1120_){
_start:
{
if (lean_obj_tag(v_as_x27_1119_) == 0)
{
return v_b_1120_;
}
else
{
lean_object* v_head_1121_; lean_object* v_tail_1122_; lean_object* v_fst_1123_; lean_object* v_snd_1124_; lean_object* v_r_1125_; 
v_head_1121_ = lean_ctor_get(v_as_x27_1119_, 0);
v_tail_1122_ = lean_ctor_get(v_as_x27_1119_, 1);
v_fst_1123_ = lean_ctor_get(v_head_1121_, 0);
v_snd_1124_ = lean_ctor_get(v_head_1121_, 1);
lean_inc(v_snd_1124_);
lean_inc(v_fst_1123_);
v_r_1125_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1___redArg(v_b_1120_, v_fst_1123_, v_snd_1124_);
v_as_x27_1119_ = v_tail_1122_;
v_b_1120_ = v_r_1125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg___boxed(lean_object* v_as_x27_1127_, lean_object* v_b_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v_as_x27_1127_, v_b_1128_);
lean_dec(v_as_x27_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(lean_object* v_m_1130_, lean_object* v_l_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v_l_1131_, v_m_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1___boxed(lean_object* v_m_1133_, lean_object* v_l_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(v_m_1133_, v_l_1134_);
lean_dec(v_l_1134_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23___redArg(lean_object* v_x_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
lean_object* v_ks_1140_; lean_object* v_vs_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1165_; 
v_ks_1140_ = lean_ctor_get(v_x_1136_, 0);
v_vs_1141_ = lean_ctor_get(v_x_1136_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1136_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1143_ = v_x_1136_;
v_isShared_1144_ = v_isSharedCheck_1165_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_vs_1141_);
lean_inc(v_ks_1140_);
lean_dec(v_x_1136_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1165_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_array_get_size(v_ks_1140_);
v___x_1146_ = lean_nat_dec_lt(v_x_1137_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
lean_dec(v_x_1137_);
v___x_1147_ = lean_array_push(v_ks_1140_, v_x_1138_);
v___x_1148_ = lean_array_push(v_vs_1141_, v_x_1139_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1148_);
lean_ctor_set(v___x_1143_, 0, v___x_1147_);
v___x_1150_ = v___x_1143_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
else
{
lean_object* v_k_x27_1152_; uint8_t v___x_1153_; 
v_k_x27_1152_ = lean_array_fget_borrowed(v_ks_1140_, v_x_1137_);
v___x_1153_ = l_Lean_instBEqMVarId_beq(v_x_1138_, v_k_x27_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1155_; 
if (v_isShared_1144_ == 0)
{
v___x_1155_ = v___x_1143_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_ks_1140_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_vs_1141_);
v___x_1155_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = lean_nat_add(v_x_1137_, v___x_1156_);
lean_dec(v_x_1137_);
v_x_1136_ = v___x_1155_;
v_x_1137_ = v___x_1157_;
goto _start;
}
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1160_ = lean_array_fset(v_ks_1140_, v_x_1137_, v_x_1138_);
v___x_1161_ = lean_array_fset(v_vs_1141_, v_x_1137_, v_x_1139_);
lean_dec(v_x_1137_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1161_);
lean_ctor_set(v___x_1143_, 0, v___x_1160_);
v___x_1163_ = v___x_1143_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v___x_1161_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20___redArg(lean_object* v_n_1166_, lean_object* v_k_1167_, lean_object* v_v_1168_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_unsigned_to_nat(0u);
v___x_1170_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23___redArg(v_n_1166_, v___x_1169_, v_k_1167_, v_v_1168_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(lean_object* v_x_1172_, size_t v_x_1173_, size_t v_x_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_){
_start:
{
if (lean_obj_tag(v_x_1172_) == 0)
{
lean_object* v_es_1177_; size_t v___x_1178_; size_t v___x_1179_; lean_object* v_j_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v_es_1177_ = lean_ctor_get(v_x_1172_, 0);
v___x_1178_ = ((size_t)31ULL);
v___x_1179_ = lean_usize_land(v_x_1173_, v___x_1178_);
v_j_1180_ = lean_usize_to_nat(v___x_1179_);
v___x_1181_ = lean_array_get_size(v_es_1177_);
v___x_1182_ = lean_nat_dec_lt(v_j_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_dec(v_j_1180_);
lean_dec(v_x_1176_);
lean_dec(v_x_1175_);
return v_x_1172_;
}
else
{
lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1221_; 
lean_inc_ref(v_es_1177_);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_x_1172_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v_x_1172_, 0);
lean_dec(v_unused_1222_);
v___x_1184_ = v_x_1172_;
v_isShared_1185_ = v_isSharedCheck_1221_;
goto v_resetjp_1183_;
}
else
{
lean_dec(v_x_1172_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1221_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v_v_1186_; lean_object* v___x_1187_; lean_object* v_xs_x27_1188_; lean_object* v___y_1190_; 
v_v_1186_ = lean_array_fget(v_es_1177_, v_j_1180_);
v___x_1187_ = lean_box(0);
v_xs_x27_1188_ = lean_array_fset(v_es_1177_, v_j_1180_, v___x_1187_);
switch(lean_obj_tag(v_v_1186_))
{
case 0:
{
lean_object* v_key_1195_; lean_object* v_val_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1206_; 
v_key_1195_ = lean_ctor_get(v_v_1186_, 0);
v_val_1196_ = lean_ctor_get(v_v_1186_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_v_1186_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1198_ = v_v_1186_;
v_isShared_1199_ = v_isSharedCheck_1206_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_val_1196_);
lean_inc(v_key_1195_);
lean_dec(v_v_1186_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1206_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
uint8_t v___x_1200_; 
v___x_1200_ = l_Lean_instBEqMVarId_beq(v_x_1175_, v_key_1195_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_del_object(v___x_1198_);
v___x_1201_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1195_, v_val_1196_, v_x_1175_, v_x_1176_);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
v___y_1190_ = v___x_1202_;
goto v___jp_1189_;
}
else
{
lean_object* v___x_1204_; 
lean_dec(v_val_1196_);
lean_dec(v_key_1195_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 1, v_x_1176_);
lean_ctor_set(v___x_1198_, 0, v_x_1175_);
v___x_1204_ = v___x_1198_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_x_1175_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_x_1176_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
v___y_1190_ = v___x_1204_;
goto v___jp_1189_;
}
}
}
}
case 1:
{
lean_object* v_node_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1219_; 
v_node_1207_ = lean_ctor_get(v_v_1186_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_v_1186_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1209_ = v_v_1186_;
v_isShared_1210_ = v_isSharedCheck_1219_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_node_1207_);
lean_dec(v_v_1186_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1219_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
size_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1211_ = ((size_t)5ULL);
v___x_1212_ = lean_usize_shift_right(v_x_1173_, v___x_1211_);
v___x_1213_ = ((size_t)1ULL);
v___x_1214_ = lean_usize_add(v_x_1174_, v___x_1213_);
v___x_1215_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_node_1207_, v___x_1212_, v___x_1214_, v_x_1175_, v_x_1176_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1215_);
v___x_1217_ = v___x_1209_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
v___y_1190_ = v___x_1217_;
goto v___jp_1189_;
}
}
}
default: 
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v_x_1175_);
lean_ctor_set(v___x_1220_, 1, v_x_1176_);
v___y_1190_ = v___x_1220_;
goto v___jp_1189_;
}
}
v___jp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = lean_array_fset(v_xs_x27_1188_, v_j_1180_, v___y_1190_);
lean_dec(v_j_1180_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1191_);
v___x_1193_ = v___x_1184_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
else
{
lean_object* v_ks_1223_; lean_object* v_vs_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1242_; 
v_ks_1223_ = lean_ctor_get(v_x_1172_, 0);
v_vs_1224_ = lean_ctor_get(v_x_1172_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_x_1172_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1226_ = v_x_1172_;
v_isShared_1227_ = v_isSharedCheck_1242_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_vs_1224_);
lean_inc(v_ks_1223_);
lean_dec(v_x_1172_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1242_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_ks_1223_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_vs_1224_);
v___x_1229_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v_newNode_1230_; size_t v___x_1231_; uint8_t v___x_1232_; 
v_newNode_1230_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20___redArg(v___x_1229_, v_x_1175_, v_x_1176_);
v___x_1231_ = ((size_t)7ULL);
v___x_1232_ = lean_usize_dec_le(v___x_1231_, v_x_1174_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1233_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1230_);
v___x_1234_ = lean_unsigned_to_nat(4u);
v___x_1235_ = lean_nat_dec_lt(v___x_1233_, v___x_1234_);
lean_dec(v___x_1233_);
if (v___x_1235_ == 0)
{
lean_object* v_ks_1236_; lean_object* v_vs_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_ks_1236_ = lean_ctor_get(v_newNode_1230_, 0);
lean_inc_ref(v_ks_1236_);
v_vs_1237_ = lean_ctor_get(v_newNode_1230_, 1);
lean_inc_ref(v_vs_1237_);
lean_dec_ref(v_newNode_1230_);
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1239_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___closed__0);
v___x_1240_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(v_x_1174_, v_ks_1236_, v_vs_1237_, v___x_1238_, v___x_1239_);
lean_dec_ref(v_vs_1237_);
lean_dec_ref(v_ks_1236_);
return v___x_1240_;
}
else
{
return v_newNode_1230_;
}
}
else
{
return v_newNode_1230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(size_t v_depth_1243_, lean_object* v_keys_1244_, lean_object* v_vals_1245_, lean_object* v_i_1246_, lean_object* v_entries_1247_){
_start:
{
lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1248_ = lean_array_get_size(v_keys_1244_);
v___x_1249_ = lean_nat_dec_lt(v_i_1246_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_dec(v_i_1246_);
return v_entries_1247_;
}
else
{
lean_object* v_k_1250_; lean_object* v_v_1251_; uint64_t v___x_1252_; size_t v_h_1253_; size_t v___x_1254_; lean_object* v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; size_t v_h_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_k_1250_ = lean_array_fget_borrowed(v_keys_1244_, v_i_1246_);
v_v_1251_ = lean_array_fget_borrowed(v_vals_1245_, v_i_1246_);
v___x_1252_ = l_Lean_instHashableMVarId_hash(v_k_1250_);
v_h_1253_ = lean_uint64_to_usize(v___x_1252_);
v___x_1254_ = ((size_t)5ULL);
v___x_1255_ = lean_unsigned_to_nat(1u);
v___x_1256_ = ((size_t)1ULL);
v___x_1257_ = lean_usize_sub(v_depth_1243_, v___x_1256_);
v___x_1258_ = lean_usize_mul(v___x_1254_, v___x_1257_);
v_h_1259_ = lean_usize_shift_right(v_h_1253_, v___x_1258_);
v___x_1260_ = lean_nat_add(v_i_1246_, v___x_1255_);
lean_dec(v_i_1246_);
lean_inc(v_v_1251_);
lean_inc(v_k_1250_);
v___x_1261_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_entries_1247_, v_h_1259_, v_depth_1243_, v_k_1250_, v_v_1251_);
v_i_1246_ = v___x_1260_;
v_entries_1247_ = v___x_1261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg___boxed(lean_object* v_depth_1263_, lean_object* v_keys_1264_, lean_object* v_vals_1265_, lean_object* v_i_1266_, lean_object* v_entries_1267_){
_start:
{
size_t v_depth_boxed_1268_; lean_object* v_res_1269_; 
v_depth_boxed_1268_ = lean_unbox_usize(v_depth_1263_);
lean_dec(v_depth_1263_);
v_res_1269_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(v_depth_boxed_1268_, v_keys_1264_, v_vals_1265_, v_i_1266_, v_entries_1267_);
lean_dec_ref(v_vals_1265_);
lean_dec_ref(v_keys_1264_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg___boxed(lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
size_t v_x_40205__boxed_1275_; size_t v_x_40206__boxed_1276_; lean_object* v_res_1277_; 
v_x_40205__boxed_1275_ = lean_unbox_usize(v_x_1271_);
lean_dec(v_x_1271_);
v_x_40206__boxed_1276_ = lean_unbox_usize(v_x_1272_);
lean_dec(v_x_1272_);
v_res_1277_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_x_1270_, v_x_40205__boxed_1275_, v_x_40206__boxed_1276_, v_x_1273_, v_x_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
uint64_t v___x_1281_; size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
v___x_1281_ = l_Lean_instHashableMVarId_hash(v_x_1279_);
v___x_1282_ = lean_uint64_to_usize(v___x_1281_);
v___x_1283_ = ((size_t)1ULL);
v___x_1284_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_x_1278_, v___x_1282_, v___x_1283_, v_x_1279_, v_x_1280_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(lean_object* v_mvarId_1285_, lean_object* v_val_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; lean_object* v_mctx_1290_; lean_object* v_cache_1291_; lean_object* v_zetaDeltaFVarIds_1292_; lean_object* v_postponed_1293_; lean_object* v_diag_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1323_; 
v___x_1289_ = lean_st_ref_take(v___y_1287_);
v_mctx_1290_ = lean_ctor_get(v___x_1289_, 0);
v_cache_1291_ = lean_ctor_get(v___x_1289_, 1);
v_zetaDeltaFVarIds_1292_ = lean_ctor_get(v___x_1289_, 2);
v_postponed_1293_ = lean_ctor_get(v___x_1289_, 3);
v_diag_1294_ = lean_ctor_get(v___x_1289_, 4);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1296_ = v___x_1289_;
v_isShared_1297_ = v_isSharedCheck_1323_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_diag_1294_);
lean_inc(v_postponed_1293_);
lean_inc(v_zetaDeltaFVarIds_1292_);
lean_inc(v_cache_1291_);
lean_inc(v_mctx_1290_);
lean_dec(v___x_1289_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1323_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_depth_1298_; lean_object* v_levelAssignDepth_1299_; lean_object* v_lmvarCounter_1300_; lean_object* v_mvarCounter_1301_; lean_object* v_lDecls_1302_; lean_object* v_decls_1303_; lean_object* v_userNames_1304_; lean_object* v_lAssignment_1305_; lean_object* v_eAssignment_1306_; lean_object* v_dAssignment_1307_; lean_object* v_instanceTypedMVars_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1322_; 
v_depth_1298_ = lean_ctor_get(v_mctx_1290_, 0);
v_levelAssignDepth_1299_ = lean_ctor_get(v_mctx_1290_, 1);
v_lmvarCounter_1300_ = lean_ctor_get(v_mctx_1290_, 2);
v_mvarCounter_1301_ = lean_ctor_get(v_mctx_1290_, 3);
v_lDecls_1302_ = lean_ctor_get(v_mctx_1290_, 4);
v_decls_1303_ = lean_ctor_get(v_mctx_1290_, 5);
v_userNames_1304_ = lean_ctor_get(v_mctx_1290_, 6);
v_lAssignment_1305_ = lean_ctor_get(v_mctx_1290_, 7);
v_eAssignment_1306_ = lean_ctor_get(v_mctx_1290_, 8);
v_dAssignment_1307_ = lean_ctor_get(v_mctx_1290_, 9);
v_instanceTypedMVars_1308_ = lean_ctor_get(v_mctx_1290_, 10);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_mctx_1290_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1310_ = v_mctx_1290_;
v_isShared_1311_ = v_isSharedCheck_1322_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_instanceTypedMVars_1308_);
lean_inc(v_dAssignment_1307_);
lean_inc(v_eAssignment_1306_);
lean_inc(v_lAssignment_1305_);
lean_inc(v_userNames_1304_);
lean_inc(v_decls_1303_);
lean_inc(v_lDecls_1302_);
lean_inc(v_mvarCounter_1301_);
lean_inc(v_lmvarCounter_1300_);
lean_inc(v_levelAssignDepth_1299_);
lean_inc(v_depth_1298_);
lean_dec(v_mctx_1290_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1322_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(v_eAssignment_1306_, v_mvarId_1285_, v_val_1286_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 8, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_depth_1298_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_levelAssignDepth_1299_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_lmvarCounter_1300_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_mvarCounter_1301_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v_lDecls_1302_);
lean_ctor_set(v_reuseFailAlloc_1321_, 5, v_decls_1303_);
lean_ctor_set(v_reuseFailAlloc_1321_, 6, v_userNames_1304_);
lean_ctor_set(v_reuseFailAlloc_1321_, 7, v_lAssignment_1305_);
lean_ctor_set(v_reuseFailAlloc_1321_, 8, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1321_, 9, v_dAssignment_1307_);
lean_ctor_set(v_reuseFailAlloc_1321_, 10, v_instanceTypedMVars_1308_);
v___x_1314_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1314_);
v___x_1316_ = v___x_1296_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_cache_1291_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_zetaDeltaFVarIds_1292_);
lean_ctor_set(v_reuseFailAlloc_1320_, 3, v_postponed_1293_);
lean_ctor_set(v_reuseFailAlloc_1320_, 4, v_diag_1294_);
v___x_1316_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = lean_st_ref_put(v___y_1287_, v___x_1316_);
v___x_1318_ = lean_box(0);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg___boxed(lean_object* v_mvarId_1324_, lean_object* v_val_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v_mvarId_1324_, v_val_1325_, v___y_1326_);
lean_dec(v___y_1326_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
if (lean_obj_tag(v_a_1329_) == 0)
{
lean_object* v___x_1331_; 
v___x_1331_ = l_List_reverse___redArg(v_a_1330_);
return v___x_1331_;
}
else
{
lean_object* v_head_1332_; lean_object* v_snd_1333_; lean_object* v_tail_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1357_; 
v_head_1332_ = lean_ctor_get(v_a_1329_, 0);
lean_inc(v_head_1332_);
v_snd_1333_ = lean_ctor_get(v_head_1332_, 1);
lean_inc(v_snd_1333_);
v_tail_1334_ = lean_ctor_get(v_a_1329_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_a_1329_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; 
v_unused_1358_ = lean_ctor_get(v_a_1329_, 0);
lean_dec(v_unused_1358_);
v___x_1336_ = v_a_1329_;
v_isShared_1337_ = v_isSharedCheck_1357_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_tail_1334_);
lean_dec(v_a_1329_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1357_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_fst_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1355_; 
v_fst_1338_ = lean_ctor_get(v_head_1332_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_head_1332_);
if (v_isSharedCheck_1355_ == 0)
{
lean_object* v_unused_1356_; 
v_unused_1356_ = lean_ctor_get(v_head_1332_, 1);
lean_dec(v_unused_1356_);
v___x_1340_ = v_head_1332_;
v_isShared_1341_ = v_isSharedCheck_1355_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_fst_1338_);
lean_dec(v_head_1332_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1355_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v_width_1342_; lean_object* v_atomNumber_1343_; uint8_t v_synthetic_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v_width_1342_ = lean_ctor_get(v_snd_1333_, 0);
lean_inc(v_width_1342_);
v_atomNumber_1343_ = lean_ctor_get(v_snd_1333_, 1);
lean_inc(v_atomNumber_1343_);
v_synthetic_1344_ = lean_ctor_get_uint8(v_snd_1333_, sizeof(void*)*2);
lean_dec(v_snd_1333_);
v___x_1345_ = lean_box(v_synthetic_1344_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 1, v___x_1345_);
v___x_1347_ = v___x_1340_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_fst_1338_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_width_1342_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v_atomNumber_1343_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 1, v_a_1330_);
lean_ctor_set(v___x_1336_, 0, v___x_1349_);
v___x_1351_ = v___x_1336_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_a_1330_);
v___x_1351_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
v_a_1329_ = v_tail_1334_;
v_a_1330_ = v___x_1351_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(lean_object* v_cls_1362_, lean_object* v_msg_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_ref_1369_; lean_object* v___x_1370_; lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1415_; 
v_ref_1369_ = lean_ctor_get(v___y_1366_, 2);
v___x_1370_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3_spec__5(v_msg_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1415_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1415_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v_traceState_1376_; lean_object* v_env_1377_; lean_object* v_nextMacroScope_1378_; lean_object* v_ngen_1379_; lean_object* v_auxDeclNGen_1380_; lean_object* v_cache_1381_; lean_object* v_messages_1382_; lean_object* v_infoState_1383_; lean_object* v_snapshotTasks_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1414_; 
v___x_1375_ = lean_st_ref_take(v___y_1367_);
v_traceState_1376_ = lean_ctor_get(v___x_1375_, 4);
v_env_1377_ = lean_ctor_get(v___x_1375_, 0);
v_nextMacroScope_1378_ = lean_ctor_get(v___x_1375_, 1);
v_ngen_1379_ = lean_ctor_get(v___x_1375_, 2);
v_auxDeclNGen_1380_ = lean_ctor_get(v___x_1375_, 3);
v_cache_1381_ = lean_ctor_get(v___x_1375_, 5);
v_messages_1382_ = lean_ctor_get(v___x_1375_, 6);
v_infoState_1383_ = lean_ctor_get(v___x_1375_, 7);
v_snapshotTasks_1384_ = lean_ctor_get(v___x_1375_, 8);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1386_ = v___x_1375_;
v_isShared_1387_ = v_isSharedCheck_1414_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snapshotTasks_1384_);
lean_inc(v_infoState_1383_);
lean_inc(v_messages_1382_);
lean_inc(v_cache_1381_);
lean_inc(v_traceState_1376_);
lean_inc(v_auxDeclNGen_1380_);
lean_inc(v_ngen_1379_);
lean_inc(v_nextMacroScope_1378_);
lean_inc(v_env_1377_);
lean_dec(v___x_1375_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1414_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
uint64_t v_tid_1388_; lean_object* v_traces_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1413_; 
v_tid_1388_ = lean_ctor_get_uint64(v_traceState_1376_, sizeof(void*)*1);
v_traces_1389_ = lean_ctor_get(v_traceState_1376_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_traceState_1376_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1391_ = v_traceState_1376_;
v_isShared_1392_ = v_isSharedCheck_1413_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_traces_1389_);
lean_dec(v_traceState_1376_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1413_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; double v___x_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1393_ = lean_box(0);
v___x_1394_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9___closed__0);
v___x_1395_ = 0;
v___x_1396_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0));
v___x_1397_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1397_, 0, v_cls_1362_);
lean_ctor_set(v___x_1397_, 1, v___x_1393_);
lean_ctor_set(v___x_1397_, 2, v___x_1396_);
lean_ctor_set_float(v___x_1397_, sizeof(void*)*3, v___x_1394_);
lean_ctor_set_float(v___x_1397_, sizeof(void*)*3 + 8, v___x_1394_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*3 + 16, v___x_1395_);
v___x_1398_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1));
v___x_1399_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1397_);
lean_ctor_set(v___x_1399_, 1, v_a_1371_);
lean_ctor_set(v___x_1399_, 2, v___x_1398_);
lean_inc(v_ref_1369_);
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_ref_1369_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___x_1401_ = l_Lean_PersistentArray_push___redArg(v_traces_1389_, v___x_1400_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1401_);
v___x_1403_ = v___x_1391_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1401_);
lean_ctor_set_uint64(v_reuseFailAlloc_1412_, sizeof(void*)*1, v_tid_1388_);
v___x_1403_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1405_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v___x_1403_);
v___x_1405_ = v___x_1386_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_env_1377_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_nextMacroScope_1378_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_ngen_1379_);
lean_ctor_set(v_reuseFailAlloc_1411_, 3, v_auxDeclNGen_1380_);
lean_ctor_set(v_reuseFailAlloc_1411_, 4, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1411_, 5, v_cache_1381_);
lean_ctor_set(v_reuseFailAlloc_1411_, 6, v_messages_1382_);
lean_ctor_set(v_reuseFailAlloc_1411_, 7, v_infoState_1383_);
lean_ctor_set(v_reuseFailAlloc_1411_, 8, v_snapshotTasks_1384_);
v___x_1405_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1406_ = lean_st_ref_put(v___y_1367_, v___x_1405_);
v___x_1407_ = lean_box(0);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1407_);
v___x_1409_ = v___x_1373_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___boxed(lean_object* v_cls_1416_, lean_object* v_msg_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(v_cls_1416_, v_msg_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
return v_res_1423_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = lean_box(0);
v___x_1425_ = lean_unsigned_to_nat(16u);
v___x_1426_ = lean_mk_array(v___x_1425_, v___x_1424_);
return v___x_1426_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0);
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
lean_ctor_set(v___x_1429_, 1, v___x_1427_);
return v___x_1429_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4));
v___x_1435_ = l_Lean_stringToMessageData(v___x_1434_);
return v___x_1435_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1436_; double v___x_1437_; 
v___x_1436_ = lean_unsigned_to_nat(1000000000u);
v___x_1437_ = lean_float_of_nat(v___x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(lean_object* v_unsatProver_1438_, lean_object* v_g_1439_, lean_object* v_cls_1440_, uint8_t v___x_1441_, lean_object* v___x_1442_, lean_object* v___f_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v_toCold_1543_; lean_object* v_options_1544_; lean_object* v_inheritedTraceOptions_1545_; uint8_t v_hasTrace_1546_; lean_object* v___y_1548_; 
v_toCold_1543_ = lean_ctor_get(v___y_1450_, 0);
v_options_1544_ = lean_ctor_get(v_toCold_1543_, 2);
v_inheritedTraceOptions_1545_ = lean_ctor_get(v_toCold_1543_, 11);
v_hasTrace_1546_ = lean_ctor_get_uint8(v_options_1544_, sizeof(void*)*1);
if (v_hasTrace_1546_ == 0)
{
lean_object* v___x_1577_; 
lean_dec_ref(v___f_1443_);
lean_dec_ref(v___x_1442_);
lean_inc(v_g_1439_);
v___x_1577_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1439_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
v___y_1548_ = v___x_1577_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v_a_1584_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v_a_1599_; 
v___x_1578_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3));
lean_inc(v_cls_1440_);
v___x_1579_ = l_Lean_Name_append(v___x_1578_, v_cls_1440_);
v___x_1580_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1545_, v_options_1544_, v___x_1579_);
lean_dec(v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = l_Lean_trace_profiler;
v___x_1650_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_options_1544_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; 
lean_dec_ref(v___f_1443_);
lean_dec_ref(v___x_1442_);
lean_inc(v_g_1439_);
v___x_1651_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1439_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
v___y_1548_ = v___x_1651_;
goto v___jp_1547_;
}
else
{
goto v___jp_1608_;
}
}
else
{
goto v___jp_1608_;
}
v___jp_1581_:
{
lean_object* v___x_1585_; double v___x_1586_; double v___x_1587_; double v___x_1588_; double v___x_1589_; double v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1585_ = lean_io_mono_nanos_now();
v___x_1586_ = lean_float_of_nat(v___y_1582_);
v___x_1587_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6);
v___x_1588_ = lean_float_div(v___x_1586_, v___x_1587_);
v___x_1589_ = lean_float_of_nat(v___x_1585_);
v___x_1590_ = lean_float_div(v___x_1589_, v___x_1587_);
v___x_1591_ = lean_box_float(v___x_1588_);
v___x_1592_ = lean_box_float(v___x_1590_);
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v_a_1584_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
lean_inc(v_cls_1440_);
v___x_1595_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(v_cls_1440_, v___x_1441_, v___x_1442_, v_options_1544_, v___x_1580_, v___y_1583_, v___f_1443_, v___x_1594_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
v___y_1548_ = v___x_1595_;
goto v___jp_1547_;
}
v___jp_1596_:
{
lean_object* v___x_1600_; double v___x_1601_; double v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1600_ = lean_io_get_num_heartbeats();
v___x_1601_ = lean_float_of_nat(v___y_1597_);
v___x_1602_ = lean_float_of_nat(v___x_1600_);
v___x_1603_ = lean_box_float(v___x_1601_);
v___x_1604_ = lean_box_float(v___x_1602_);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1603_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v_a_1599_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
lean_inc(v_cls_1440_);
v___x_1607_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9(v_cls_1440_, v___x_1441_, v___x_1442_, v_options_1544_, v___x_1580_, v___y_1598_, v___f_1443_, v___x_1606_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
v___y_1548_ = v___x_1607_;
goto v___jp_1547_;
}
v___jp_1608_:
{
lean_object* v___x_1609_; lean_object* v_a_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1609_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___redArg(v___y_1451_);
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1612_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_options_1544_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = lean_io_mono_nanos_now();
lean_inc(v_g_1439_);
v___x_1614_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1439_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
lean_ctor_set_tag(v___x_1617_, 1);
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
v___y_1582_ = v___x_1613_;
v___y_1583_ = v_a_1610_;
v_a_1584_ = v___x_1620_;
goto v___jp_1581_;
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
v_a_1623_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1614_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1614_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 0);
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
v___y_1582_ = v___x_1613_;
v___y_1583_ = v_a_1610_;
v_a_1584_ = v___x_1628_;
goto v___jp_1581_;
}
}
}
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_io_get_num_heartbeats();
lean_inc(v_g_1439_);
v___x_1632_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1439_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 1);
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
v___y_1597_ = v___x_1631_;
v___y_1598_ = v_a_1610_;
v_a_1599_ = v___x_1638_;
goto v___jp_1596_;
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
v_a_1641_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1632_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1632_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 0);
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
v___y_1597_ = v___x_1631_;
v___y_1598_ = v_a_1610_;
v_a_1599_ = v___x_1646_;
goto v___jp_1596_;
}
}
}
}
}
}
v___jp_1453_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1464_ = lean_box(0);
v___x_1465_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v___y_1463_, v___x_1464_);
v___x_1466_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1);
v___x_1467_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v___x_1465_, v___x_1466_);
lean_dec(v___x_1465_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1456_);
lean_inc(v___y_1462_);
lean_inc_ref(v___y_1460_);
lean_inc_ref(v___y_1455_);
lean_inc(v_g_1439_);
v___x_1468_ = lean_apply_8(v_unsatProver_1438_, v_g_1439_, v___y_1455_, v___x_1467_, v___y_1460_, v___y_1462_, v___y_1456_, v___y_1461_, lean_box(0));
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1514_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1514_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1514_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
if (lean_obj_tag(v_a_1469_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref(v___y_1455_);
lean_dec(v_g_1439_);
v_a_1473_ = lean_ctor_get(v_a_1469_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_a_1469_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1475_ = v_a_1469_;
v_isShared_1476_ = v_isSharedCheck_1483_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v_a_1469_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1483_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1478_);
v___x_1480_ = v___x_1471_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1513_; 
lean_del_object(v___x_1471_);
v_a_1484_ = lean_ctor_get(v_a_1469_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_a_1469_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1486_ = v_a_1469_;
v_isShared_1487_ = v_isSharedCheck_1513_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v_a_1469_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1513_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_proof_1488_; lean_object* v_cert_1489_; lean_object* v_proveFalse_1490_; lean_object* v___x_1491_; 
v_proof_1488_ = lean_ctor_get(v_a_1484_, 0);
lean_inc_ref(v_proof_1488_);
v_cert_1489_ = lean_ctor_get(v_a_1484_, 1);
lean_inc(v_cert_1489_);
lean_dec(v_a_1484_);
v_proveFalse_1490_ = lean_ctor_get(v___y_1455_, 1);
lean_inc_ref(v_proveFalse_1490_);
lean_dec_ref(v___y_1455_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1456_);
lean_inc(v___y_1462_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1454_);
lean_inc_ref(v___y_1459_);
v___x_1491_ = lean_apply_10(v_proveFalse_1490_, v_proof_1488_, v___y_1459_, v___y_1454_, v___y_1458_, v___y_1457_, v___y_1460_, v___y_1462_, v___y_1456_, v___y_1461_, lean_box(0));
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1503_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1493_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v_g_1439_, v_a_1492_, v___y_1462_);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v___x_1493_, 0);
lean_dec(v_unused_1504_);
v___x_1495_ = v___x_1493_;
v_isShared_1496_ = v_isSharedCheck_1503_;
goto v_resetjp_1494_;
}
else
{
lean_dec(v___x_1493_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1503_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v_cert_1489_);
v___x_1498_ = v___x_1486_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_cert_1489_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1498_);
v___x_1500_ = v___x_1495_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_cert_1489_);
lean_del_object(v___x_1486_);
lean_dec(v_g_1439_);
v_a_1505_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1491_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1491_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec_ref(v___y_1455_);
lean_dec(v_g_1439_);
v_a_1515_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1468_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1468_);
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
v___jp_1523_:
{
lean_object* v___x_1533_; lean_object* v_atoms_1534_; lean_object* v_buckets_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1533_ = lean_st_ref_get(v___y_1526_);
v_atoms_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc_ref(v_atoms_1534_);
lean_dec(v___x_1533_);
v_buckets_1535_ = lean_ctor_get(v_atoms_1534_, 1);
lean_inc_ref(v_buckets_1535_);
lean_dec_ref(v_atoms_1534_);
v___x_1536_ = lean_box(0);
v___x_1537_ = lean_array_get_size(v_buckets_1535_);
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = lean_nat_dec_lt(v___x_1538_, v___x_1537_);
if (v___x_1539_ == 0)
{
lean_dec_ref(v_buckets_1535_);
v___y_1454_ = v___y_1526_;
v___y_1455_ = v___y_1524_;
v___y_1456_ = v___y_1531_;
v___y_1457_ = v___y_1528_;
v___y_1458_ = v___y_1527_;
v___y_1459_ = v___y_1525_;
v___y_1460_ = v___y_1529_;
v___y_1461_ = v___y_1532_;
v___y_1462_ = v___y_1530_;
v___y_1463_ = v___x_1536_;
goto v___jp_1453_;
}
else
{
size_t v___x_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = lean_usize_of_nat(v___x_1537_);
v___x_1541_ = ((size_t)0ULL);
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_buckets_1535_, v___x_1540_, v___x_1541_, v___x_1536_);
lean_dec_ref(v_buckets_1535_);
v___y_1454_ = v___y_1526_;
v___y_1455_ = v___y_1524_;
v___y_1456_ = v___y_1531_;
v___y_1457_ = v___y_1528_;
v___y_1458_ = v___y_1527_;
v___y_1459_ = v___y_1525_;
v___y_1460_ = v___y_1529_;
v___y_1461_ = v___y_1532_;
v___y_1462_ = v___y_1530_;
v___y_1463_ = v___x_1542_;
goto v___jp_1453_;
}
}
v___jp_1547_:
{
if (lean_obj_tag(v___y_1548_) == 0)
{
if (v_hasTrace_1546_ == 0)
{
lean_object* v_a_1549_; 
lean_dec(v_cls_1440_);
v_a_1549_ = lean_ctor_get(v___y_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___y_1548_, 1);
v___y_1524_ = v_a_1549_;
v___y_1525_ = v___y_1444_;
v___y_1526_ = v___y_1445_;
v___y_1527_ = v___y_1446_;
v___y_1528_ = v___y_1447_;
v___y_1529_ = v___y_1448_;
v___y_1530_ = v___y_1449_;
v___y_1531_ = v___y_1450_;
v___y_1532_ = v___y_1451_;
goto v___jp_1523_;
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v_a_1550_ = lean_ctor_get(v___y_1548_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___y_1548_, 1);
v___x_1551_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3));
lean_inc(v_cls_1440_);
v___x_1552_ = l_Lean_Name_append(v___x_1551_, v_cls_1440_);
v___x_1553_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1545_, v_options_1544_, v___x_1552_);
lean_dec(v___x_1552_);
if (v___x_1553_ == 0)
{
lean_dec(v_cls_1440_);
v___y_1524_ = v_a_1550_;
v___y_1525_ = v___y_1444_;
v___y_1526_ = v___y_1445_;
v___y_1527_ = v___y_1446_;
v___y_1528_ = v___y_1447_;
v___y_1529_ = v___y_1448_;
v___y_1530_ = v___y_1449_;
v___y_1531_ = v___y_1450_;
v___y_1532_ = v___y_1451_;
goto v___jp_1523_;
}
else
{
lean_object* v_bvExpr_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_bvExpr_1554_ = lean_ctor_get(v_a_1550_, 0);
v___x_1555_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5);
lean_inc_ref(v_bvExpr_1554_);
v___x_1556_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_bvExpr_1554_);
v___x_1557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
v___x_1558_ = l_Lean_MessageData_ofFormat(v___x_1557_);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1555_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(v_cls_1440_, v___x_1559_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_dec_ref_known(v___x_1560_, 1);
v___y_1524_ = v_a_1550_;
v___y_1525_ = v___y_1444_;
v___y_1526_ = v___y_1445_;
v___y_1527_ = v___y_1446_;
v___y_1528_ = v___y_1447_;
v___y_1529_ = v___y_1448_;
v___y_1530_ = v___y_1449_;
v___y_1531_ = v___y_1450_;
v___y_1532_ = v___y_1451_;
goto v___jp_1523_;
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec(v_a_1550_);
lean_dec(v_g_1439_);
lean_dec_ref(v_unsatProver_1438_);
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v_cls_1440_);
lean_dec(v_g_1439_);
lean_dec_ref(v_unsatProver_1438_);
v_a_1569_ = lean_ctor_get(v___y_1548_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___y_1548_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___y_1548_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___y_1548_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed(lean_object* v_unsatProver_1652_, lean_object* v_g_1653_, lean_object* v_cls_1654_, lean_object* v___x_1655_, lean_object* v___x_1656_, lean_object* v___f_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
uint8_t v___x_40604__boxed_1667_; lean_object* v_res_1668_; 
v___x_40604__boxed_1667_ = lean_unbox(v___x_1655_);
v_res_1668_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(v_unsatProver_1652_, v_g_1653_, v_cls_1654_, v___x_40604__boxed_1667_, v___x_1656_, v___f_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(lean_object* v_g_1677_, lean_object* v_unsatProver_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v___f_1688_; lean_object* v_cls_1689_; uint8_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___f_1693_; lean_object* v___x_1694_; 
v___f_1688_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0));
v_cls_1689_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4));
v___x_1690_ = 1;
v___x_1691_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0));
v___x_1692_ = lean_box(v___x_1690_);
lean_inc(v_g_1677_);
v___f_1693_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed), 15, 6);
lean_closure_set(v___f_1693_, 0, v_unsatProver_1678_);
lean_closure_set(v___f_1693_, 1, v_g_1677_);
lean_closure_set(v___f_1693_, 2, v_cls_1689_);
lean_closure_set(v___f_1693_, 3, v___x_1692_);
lean_closure_set(v___f_1693_, 4, v___x_1691_);
lean_closure_set(v___f_1693_, 5, v___f_1688_);
v___x_1694_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_g_1677_, v___f_1693_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___boxed(lean_object* v_g_1695_, lean_object* v_unsatProver_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1695_, v_unsatProver_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(lean_object* v_00_u03b1_1707_, lean_object* v_g_1708_, lean_object* v_unsatProver_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1708_, v_unsatProver_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed(lean_object* v_00_u03b1_1720_, lean_object* v_g_1721_, lean_object* v_unsatProver_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(v_00_u03b1_1720_, v_g_1721_, v_unsatProver_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(lean_object* v_mvarId_1733_, lean_object* v_val_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___redArg(v_mvarId_1733_, v_val_1734_, v___y_1740_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___boxed(lean_object* v_mvarId_1745_, lean_object* v_val_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(v_mvarId_1745_, v_val_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6(lean_object* v_cls_1757_, lean_object* v_msg_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(v_cls_1757_, v_msg_1758_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___boxed(lean_object* v_cls_1769_, lean_object* v_msg_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6(v_cls_1769_, v_msg_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13(lean_object* v_00_u03b1_1781_, lean_object* v_x_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___redArg(v_x_1782_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1793_, lean_object* v_x_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__13(v_00_u03b1_1793_, v_x_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1(lean_object* v_00_u03b2_1805_, lean_object* v_m_1806_, lean_object* v_a_1807_, lean_object* v_b_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1___redArg(v_m_1806_, v_a_1807_, v_b_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2(lean_object* v_as_1810_, lean_object* v_as_x27_1811_, lean_object* v_b_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___redArg(v_as_x27_1811_, v_b_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2___boxed(lean_object* v_as_1815_, lean_object* v_as_x27_1816_, lean_object* v_b_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__2(v_as_1815_, v_as_x27_1816_, v_b_1817_, v_a_1818_);
lean_dec(v_as_x27_1816_);
lean_dec(v_as_1815_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4(lean_object* v_00_u03b2_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v_x_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(v_x_1821_, v_x_1822_, v_x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12(lean_object* v_oldTraces_1825_, lean_object* v_data_1826_, lean_object* v_ref_1827_, lean_object* v_msg_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___redArg(v_oldTraces_1825_, v_data_1826_, v_ref_1827_, v_msg_1828_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12___boxed(lean_object* v_oldTraces_1839_, lean_object* v_data_1840_, lean_object* v_ref_1841_, lean_object* v_msg_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__9_spec__12(v_oldTraces_1839_, v_data_1840_, v_ref_1841_, v_msg_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
return v_res_1852_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_1853_, lean_object* v_a_1854_, lean_object* v_x_1855_){
_start:
{
uint8_t v___x_1856_; 
v___x_1856_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___redArg(v_a_1854_, v_x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1857_, lean_object* v_a_1858_, lean_object* v_x_1859_){
_start:
{
uint8_t v_res_1860_; lean_object* v_r_1861_; 
v_res_1860_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__4(v_00_u03b2_1857_, v_a_1858_, v_x_1859_);
lean_dec(v_x_1859_);
lean_dec(v_a_1858_);
v_r_1861_ = lean_box(v_res_1860_);
return v_r_1861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_1862_, lean_object* v_data_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5___redArg(v_data_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_1865_, lean_object* v_a_1866_, lean_object* v_b_1867_, lean_object* v_x_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__6___redArg(v_a_1866_, v_b_1867_, v_x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10(lean_object* v_00_u03b2_1870_, lean_object* v_x_1871_, size_t v_x_1872_, size_t v_x_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___redArg(v_x_1871_, v_x_1872_, v_x_1873_, v_x_1874_, v_x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10___boxed(lean_object* v_00_u03b2_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
size_t v_x_41235__boxed_1883_; size_t v_x_41236__boxed_1884_; lean_object* v_res_1885_; 
v_x_41235__boxed_1883_ = lean_unbox_usize(v_x_1879_);
lean_dec(v_x_1879_);
v_x_41236__boxed_1884_ = lean_unbox_usize(v_x_1880_);
lean_dec(v_x_1880_);
v_res_1885_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10(v_00_u03b2_1877_, v_x_1878_, v_x_41235__boxed_1883_, v_x_41236__boxed_1884_, v_x_1881_, v_x_1882_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15(lean_object* v_00_u03b2_1886_, lean_object* v_i_1887_, lean_object* v_source_1888_, lean_object* v_target_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15___redArg(v_i_1887_, v_source_1888_, v_target_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20(lean_object* v_00_u03b2_1891_, lean_object* v_n_1892_, lean_object* v_k_1893_, lean_object* v_v_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20___redArg(v_n_1892_, v_k_1893_, v_v_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21(lean_object* v_00_u03b2_1896_, size_t v_depth_1897_, lean_object* v_keys_1898_, lean_object* v_vals_1899_, lean_object* v_heq_1900_, lean_object* v_i_1901_, lean_object* v_entries_1902_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___redArg(v_depth_1897_, v_keys_1898_, v_vals_1899_, v_i_1901_, v_entries_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21___boxed(lean_object* v_00_u03b2_1904_, lean_object* v_depth_1905_, lean_object* v_keys_1906_, lean_object* v_vals_1907_, lean_object* v_heq_1908_, lean_object* v_i_1909_, lean_object* v_entries_1910_){
_start:
{
size_t v_depth_boxed_1911_; lean_object* v_res_1912_; 
v_depth_boxed_1911_ = lean_unbox_usize(v_depth_1905_);
lean_dec(v_depth_1905_);
v_res_1912_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__21(v_00_u03b2_1904_, v_depth_boxed_1911_, v_keys_1906_, v_vals_1907_, v_heq_1908_, v_i_1909_, v_entries_1910_);
lean_dec_ref(v_vals_1907_);
lean_dec_ref(v_keys_1906_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19(lean_object* v_00_u03b2_1913_, lean_object* v_x_1914_, lean_object* v_x_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1_spec__1_spec__5_spec__15_spec__19___redArg(v_x_1914_, v_x_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23(lean_object* v_00_u03b2_1917_, lean_object* v_x_1918_, lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4_spec__10_spec__20_spec__23___redArg(v_x_1918_, v_x_1919_, v_x_1920_, v_x_1921_);
return v___x_1922_;
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
