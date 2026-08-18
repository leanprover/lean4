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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_Gate_toString(uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ShareCommon_shareCommon___redArg(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___redArg___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__0_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__4;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Reflecting goal into BVLogicalExpr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__4_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__5_value;
static const lean_string_object l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "(if "};
static const lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__14___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__15___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__19_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__19___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__20___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Reflected bv logical expression: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__7;
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__20(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__19_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg___lam__0___boxed(lean_object* v_x_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg___lam__0(v_x_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg(lean_object* v_mvarId_23_, lean_object* v_x_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___f_34_; lean_object* v___x_35_; 
lean_inc(v___y_28_);
lean_inc_ref(v___y_27_);
lean_inc(v___y_26_);
lean_inc_ref(v___y_25_);
v___f_34_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg___lam__0___boxed), 10, 5);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg___boxed(lean_object* v_mvarId_44_, lean_object* v_x_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg(v_mvarId_44_, v_x_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5(lean_object* v_00_u03b1_56_, lean_object* v_mvarId_57_, lean_object* v_x_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg(v_mvarId_57_, v_x_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___boxed(lean_object* v_00_u03b1_69_, lean_object* v_mvarId_70_, lean_object* v_x_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5(v_00_u03b1_69_, v_mvarId_70_, v_x_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(lean_object* v_m_82_, lean_object* v_query_83_, lean_object* v_x_84_, lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_zero_87_; uint8_t v_isZero_88_; 
v_zero_87_ = lean_unsigned_to_nat(0u);
v_isZero_88_ = lean_nat_dec_eq(v_x_85_, v_zero_87_);
if (v_isZero_88_ == 1)
{
lean_dec(v_x_86_);
lean_dec(v_x_85_);
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(2);
return v___x_89_;
}
else
{
lean_object* v_val_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v_val_90_ = lean_ctor_get(v_x_84_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_84_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v_x_84_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_val_90_);
lean_dec(v_x_84_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_val_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
else
{
lean_object* v_keyArray_98_; lean_object* v_valueArray_99_; lean_object* v___x_100_; uint8_t v_isSome_101_; 
v_keyArray_98_ = lean_ctor_get(v_m_82_, 1);
v_valueArray_99_ = lean_ctor_get(v_m_82_, 2);
v___x_100_ = lean_array_fget_borrowed(v_keyArray_98_, v_x_86_);
v_isSome_101_ = lean_noption_is_some(v___x_100_);
if (v_isSome_101_ == 0)
{
lean_dec(v_x_85_);
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_x_86_);
return v___x_102_;
}
else
{
lean_object* v_val_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
lean_dec(v_x_86_);
v_val_103_ = lean_ctor_get(v_x_84_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v_x_84_);
if (v_isSharedCheck_110_ == 0)
{
v___x_105_ = v_x_84_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_val_103_);
lean_dec(v_x_84_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_val_103_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
else
{
lean_object* v_one_111_; lean_object* v_n_112_; lean_object* v___y_114_; 
v_one_111_ = lean_unsigned_to_nat(1u);
v_n_112_ = lean_nat_sub(v_x_85_, v_one_111_);
lean_dec(v_x_85_);
if (v_isSome_101_ == 0)
{
goto v___jp_120_;
}
else
{
lean_object* v___x_122_; uint8_t v_isSome_123_; 
v___x_122_ = lean_array_fget_borrowed(v_valueArray_99_, v_x_86_);
v_isSome_123_ = lean_noption_is_some(v___x_122_);
if (v_isSome_123_ == 0)
{
goto v___jp_120_;
}
else
{
lean_object* v_val_124_; lean_object* v_type_125_; lean_object* v_type_126_; uint8_t v___x_127_; 
lean_inc(v___x_100_);
v_val_124_ = lean_noption_get(v___x_100_);
v_type_125_ = lean_ctor_get(v_val_124_, 1);
lean_inc_ref(v_type_125_);
v_type_126_ = lean_ctor_get(v_query_83_, 1);
v___x_127_ = lean_expr_eqv(v_type_125_, v_type_126_);
lean_dec_ref(v_type_125_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
lean_dec(v_val_124_);
v___x_128_ = lean_array_get_size(v_keyArray_98_);
v___x_129_ = lean_nat_add(v_x_86_, v_one_111_);
lean_dec(v_x_86_);
v___x_130_ = lean_nat_dec_lt(v___x_129_, v___x_128_);
if (v___x_130_ == 0)
{
lean_dec(v___x_129_);
v_x_85_ = v_n_112_;
v_x_86_ = v_zero_87_;
goto _start;
}
else
{
v_x_85_ = v_n_112_;
v_x_86_ = v___x_129_;
goto _start;
}
}
else
{
lean_object* v_val_133_; lean_object* v___x_134_; 
lean_dec(v_n_112_);
lean_dec(v_x_84_);
lean_inc(v___x_122_);
v_val_133_ = lean_noption_get(v___x_122_);
v___x_134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_134_, 0, v_x_86_);
lean_ctor_set(v___x_134_, 1, v_val_124_);
lean_ctor_set(v___x_134_, 2, v_val_133_);
return v___x_134_;
}
}
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_115_ = lean_array_get_size(v_keyArray_98_);
v___x_116_ = lean_nat_add(v_x_86_, v_one_111_);
lean_dec(v_x_86_);
v___x_117_ = lean_nat_dec_lt(v___x_116_, v___x_115_);
if (v___x_117_ == 0)
{
lean_dec(v___x_116_);
v_x_84_ = v___y_114_;
v_x_85_ = v_n_112_;
v_x_86_ = v_zero_87_;
goto _start;
}
else
{
v_x_84_ = v___y_114_;
v_x_85_ = v_n_112_;
v_x_86_ = v___x_116_;
goto _start;
}
}
v___jp_120_:
{
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v___x_121_; 
lean_inc(v_x_86_);
v___x_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_121_, 0, v_x_86_);
v___y_114_ = v___x_121_;
goto v___jp_113_;
}
else
{
v___y_114_ = v_x_84_;
goto v___jp_113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg___boxed(lean_object* v_m_135_, lean_object* v_query_136_, lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_m_135_, v_query_136_, v_x_137_, v_x_138_, v_x_139_);
lean_dec_ref(v_query_136_);
lean_dec_ref(v_m_135_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(lean_object* v_m_141_, lean_object* v_query_142_){
_start:
{
lean_object* v_keyArray_143_; lean_object* v_type_144_; lean_object* v___x_145_; uint64_t v___x_146_; uint64_t v___x_147_; uint64_t v___x_148_; uint64_t v_fold_149_; uint64_t v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_keyArray_143_ = lean_ctor_get(v_m_141_, 1);
v_type_144_ = lean_ctor_get(v_query_142_, 1);
v___x_145_ = lean_array_get_size(v_keyArray_143_);
v___x_146_ = l_Lean_Expr_hash(v_type_144_);
v___x_147_ = 32ULL;
v___x_148_ = lean_uint64_shift_right(v___x_146_, v___x_147_);
v_fold_149_ = lean_uint64_xor(v___x_146_, v___x_148_);
v___x_150_ = 16ULL;
v___x_151_ = lean_uint64_shift_right(v_fold_149_, v___x_150_);
v___x_152_ = lean_uint64_xor(v_fold_149_, v___x_151_);
v___x_153_ = lean_uint64_to_usize(v___x_152_);
v___x_154_ = lean_usize_of_nat(v___x_145_);
v___x_155_ = ((size_t)1ULL);
v___x_156_ = lean_usize_sub(v___x_154_, v___x_155_);
v___x_157_ = lean_usize_land(v___x_153_, v___x_156_);
v___x_158_ = lean_usize_to_nat(v___x_157_);
v___x_159_ = lean_box(0);
v___x_160_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_m_141_, v_query_142_, v___x_159_, v___x_145_, v___x_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg___boxed(lean_object* v_m_161_, lean_object* v_query_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_m_161_, v_query_162_);
lean_dec_ref(v_query_162_);
lean_dec_ref(v_m_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2_spec__4___redArg(lean_object* v_b_164_, lean_object* v_acc_165_, lean_object* v_i_166_){
_start:
{
lean_object* v___y_168_; lean_object* v_keyArray_176_; lean_object* v_valueArray_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_keyArray_176_ = lean_ctor_get(v_b_164_, 1);
v_valueArray_177_ = lean_ctor_get(v_b_164_, 2);
v___x_178_ = lean_array_get_size(v_keyArray_176_);
v___x_179_ = lean_nat_dec_lt(v_i_166_, v___x_178_);
if (v___x_179_ == 0)
{
lean_dec(v_i_166_);
return v_acc_165_;
}
else
{
lean_object* v___x_180_; uint8_t v_isSome_181_; 
v___x_180_ = lean_array_fget_borrowed(v_keyArray_176_, v_i_166_);
v_isSome_181_ = lean_noption_is_some(v___x_180_);
if (v_isSome_181_ == 0)
{
goto v___jp_172_;
}
else
{
lean_object* v___x_182_; uint8_t v_isSome_183_; 
v___x_182_ = lean_array_fget_borrowed(v_valueArray_177_, v_i_166_);
v_isSome_183_ = lean_noption_is_some(v___x_182_);
if (v_isSome_183_ == 0)
{
goto v___jp_172_;
}
else
{
lean_object* v_val_184_; lean_object* v_val_185_; lean_object* v_i_187_; lean_object* v___x_192_; 
lean_inc(v___x_180_);
v_val_184_ = lean_noption_get(v___x_180_);
lean_inc(v___x_182_);
v_val_185_ = lean_noption_get(v___x_182_);
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_acc_165_, v_val_184_);
switch(lean_obj_tag(v___x_192_))
{
case 0:
{
lean_object* v_index_193_; lean_object* v_size_194_; lean_object* v___x_195_; 
v_index_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_index_193_);
lean_dec_ref_known(v___x_192_, 3);
v_size_194_ = lean_ctor_get(v_acc_165_, 0);
lean_inc(v_size_194_);
v___x_195_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_165_, v_size_194_, v_index_193_, v_val_184_, v_val_185_);
lean_dec(v_index_193_);
v___y_168_ = v___x_195_;
goto v___jp_167_;
}
case 1:
{
lean_object* v_index_196_; 
v_index_196_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_index_196_);
lean_dec_ref_known(v___x_192_, 1);
v_i_187_ = v_index_196_;
goto v___jp_186_;
}
default: 
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_165_, v___x_197_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_index_199_; 
v_index_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_index_199_);
lean_dec_ref_known(v___x_198_, 1);
v_i_187_ = v_index_199_;
goto v___jp_186_;
}
else
{
lean_dec(v_val_185_);
lean_dec(v_val_184_);
v___y_168_ = v_acc_165_;
goto v___jp_167_;
}
}
}
v___jp_186_:
{
lean_object* v_size_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_size_188_ = lean_ctor_get(v_acc_165_, 0);
v___x_189_ = lean_unsigned_to_nat(1u);
v___x_190_ = lean_nat_add(v_size_188_, v___x_189_);
v___x_191_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_165_, v___x_190_, v_i_187_, v_val_184_, v_val_185_);
lean_dec(v_i_187_);
v___y_168_ = v___x_191_;
goto v___jp_167_;
}
}
}
}
v___jp_167_:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_nat_add(v_i_166_, v___x_169_);
lean_dec(v_i_166_);
v_acc_165_ = v___y_168_;
v_i_166_ = v___x_170_;
goto _start;
}
v___jp_172_:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_i_166_, v___x_173_);
lean_dec(v_i_166_);
v_i_166_ = v___x_174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_b_200_, lean_object* v_acc_201_, lean_object* v_i_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2_spec__4___redArg(v_b_200_, v_acc_201_, v_i_202_);
lean_dec_ref(v_b_200_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2___redArg(lean_object* v_init_204_, lean_object* v_b_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2_spec__4___redArg(v_b_205_, v_init_204_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2___redArg___boxed(lean_object* v_init_208_, lean_object* v_b_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2___redArg(v_init_208_, v_b_209_);
lean_dec_ref(v_b_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___redArg(lean_object* v_m_211_){
_start:
{
lean_object* v_keyArray_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_cellCount_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_target_219_; lean_object* v___x_220_; 
v_keyArray_212_ = lean_ctor_get(v_m_211_, 1);
v___x_213_ = lean_array_get_size(v_keyArray_212_);
v___x_214_ = lean_unsigned_to_nat(2u);
v_cellCount_215_ = lean_nat_mul(v___x_213_, v___x_214_);
v___x_216_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_215_);
v___x_217_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_215_);
v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_215_);
v_target_219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_219_, 0, v___x_216_);
lean_ctor_set(v_target_219_, 1, v___x_217_);
lean_ctor_set(v_target_219_, 2, v___x_218_);
v___x_220_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2___redArg(v_target_219_, v_m_211_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___redArg___boxed(lean_object* v_m_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___redArg(v_m_221_);
lean_dec_ref(v_m_221_);
return v_res_222_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__2(void){
_start:
{
lean_object* v_cellCount_226_; lean_object* v___x_227_; 
v_cellCount_226_ = lean_unsigned_to_nat(16u);
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_226_);
return v___x_227_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__3(void){
_start:
{
lean_object* v_cellCount_228_; lean_object* v___x_229_; 
v_cellCount_228_ = lean_unsigned_to_nat(16u);
v___x_229_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_228_);
return v___x_229_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__4(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_230_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__3);
v___x_231_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__2);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_231_);
lean_ctor_set(v___x_233_, 2, v___x_230_);
return v___x_233_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__5(void){
_start:
{
lean_object* v___x_234_; lean_object* v_sats_235_; lean_object* v___x_236_; 
v___x_234_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__4);
v_sats_235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__1));
v___x_236_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_236_, 0, v_sats_235_);
lean_ctor_set(v___x_236_, 1, v___x_234_);
lean_ctor_set(v___x_236_, 2, v___x_234_);
lean_ctor_set(v___x_236_, 3, v___x_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(lean_object* v_as_237_, size_t v_sz_238_, size_t v_i_239_, lean_object* v_b_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_a_251_; uint8_t v___x_255_; 
v___x_255_ = lean_usize_dec_lt(v_i_239_, v_sz_238_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v_b_240_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__0));
v___x_258_ = l_Lean_Core_checkSystem(v___x_257_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_259_; lean_object* v_a_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec_ref_known(v___x_258_, 1);
v___x_259_ = lean_unsigned_to_nat(0u);
v_a_260_ = lean_array_uget_borrowed(v_as_237_, v_i_239_);
lean_inc(v_a_260_);
v___x_261_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed), 11, 1);
lean_closure_set(v___x_261_, 0, v_a_260_);
v___x_262_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__5);
v___x_263_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v___x_261_, v___x_262_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v_fst_265_; lean_object* v_snd_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_347_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_263_, 1);
v_fst_265_ = lean_ctor_get(v_a_264_, 0);
v_snd_266_ = lean_ctor_get(v_a_264_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_a_264_);
if (v_isSharedCheck_347_ == 0)
{
v___x_268_ = v_a_264_;
v_isShared_269_ = v_isSharedCheck_347_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_snd_266_);
lean_inc(v_fst_265_);
lean_dec(v_a_264_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_347_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v_fst_270_; lean_object* v_snd_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_346_; 
v_fst_270_ = lean_ctor_get(v_b_240_, 0);
v_snd_271_ = lean_ctor_get(v_b_240_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v_b_240_);
if (v_isSharedCheck_346_ == 0)
{
v___x_273_ = v_b_240_;
v_isShared_274_ = v_isSharedCheck_346_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_snd_271_);
lean_inc(v_fst_270_);
lean_dec(v_b_240_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_346_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___y_276_; 
if (lean_obj_tag(v_fst_265_) == 1)
{
lean_object* v_val_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
lean_del_object(v___x_273_);
v_val_280_ = lean_ctor_get(v_fst_265_, 0);
lean_inc(v_val_280_);
lean_dec_ref_known(v_fst_265_, 1);
v___x_281_ = l_Array_append___redArg(v_fst_270_, v_snd_266_);
lean_dec(v_snd_266_);
v___x_282_ = lean_array_push(v___x_281_, v_val_280_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 1, v_snd_271_);
lean_ctor_set(v___x_268_, 0, v___x_282_);
v___x_284_ = v___x_268_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_snd_271_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
v_a_251_ = v___x_284_;
goto v___jp_250_;
}
}
else
{
lean_object* v___x_286_; lean_object* v___y_288_; lean_object* v_i_289_; lean_object* v___y_295_; lean_object* v___y_304_; lean_object* v_i_305_; lean_object* v___x_319_; 
lean_del_object(v___x_268_);
lean_dec(v_snd_266_);
lean_dec(v_fst_265_);
v___x_286_ = lean_box(0);
v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_snd_271_, v_a_260_);
switch(lean_obj_tag(v___x_319_))
{
case 0:
{
lean_dec_ref_known(v___x_319_, 3);
v___y_276_ = v_snd_271_;
goto v___jp_275_;
}
case 1:
{
lean_object* v_index_320_; lean_object* v_size_321_; lean_object* v_keyArray_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_index_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_index_320_);
lean_dec_ref_known(v___x_319_, 1);
v_size_321_ = lean_ctor_get(v_snd_271_, 0);
v_keyArray_322_ = lean_ctor_get(v_snd_271_, 1);
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_nat_add(v_size_321_, v___x_323_);
v___x_325_ = lean_array_get_size(v_keyArray_322_);
v___x_326_ = lean_nat_dec_lt(v___x_324_, v___x_325_);
if (v___x_326_ == 0)
{
lean_dec(v___x_324_);
lean_dec(v_index_320_);
goto v___jp_310_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_327_ = lean_unsigned_to_nat(4u);
v___x_328_ = lean_nat_mul(v___x_324_, v___x_327_);
v___x_329_ = lean_unsigned_to_nat(3u);
v___x_330_ = lean_nat_mul(v___x_325_, v___x_329_);
v___x_331_ = lean_nat_dec_le(v___x_328_, v___x_330_);
lean_dec(v___x_330_);
lean_dec(v___x_328_);
if (v___x_331_ == 0)
{
lean_dec(v___x_324_);
lean_dec(v_index_320_);
goto v___jp_310_;
}
else
{
lean_object* v___x_332_; 
lean_inc(v_a_260_);
v___x_332_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_271_, v___x_324_, v_index_320_, v_a_260_, v___x_286_);
lean_dec(v_index_320_);
v___y_276_ = v___x_332_;
goto v___jp_275_;
}
}
}
default: 
{
lean_object* v_size_333_; lean_object* v_keyArray_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_size_333_ = lean_ctor_get(v_snd_271_, 0);
v_keyArray_334_ = lean_ctor_get(v_snd_271_, 1);
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_add(v_size_333_, v___x_335_);
v___x_337_ = lean_array_get_size(v_keyArray_334_);
v___x_338_ = lean_nat_dec_lt(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
lean_dec(v___x_336_);
v___x_339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___redArg(v_snd_271_);
lean_dec(v_snd_271_);
v___y_295_ = v___x_339_;
goto v___jp_294_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_340_ = lean_unsigned_to_nat(4u);
v___x_341_ = lean_nat_mul(v___x_336_, v___x_340_);
lean_dec(v___x_336_);
v___x_342_ = lean_unsigned_to_nat(3u);
v___x_343_ = lean_nat_mul(v___x_337_, v___x_342_);
v___x_344_ = lean_nat_dec_le(v___x_341_, v___x_343_);
lean_dec(v___x_343_);
lean_dec(v___x_341_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
v___x_345_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___redArg(v_snd_271_);
lean_dec(v_snd_271_);
v___y_295_ = v___x_345_;
goto v___jp_294_;
}
else
{
v___y_295_ = v_snd_271_;
goto v___jp_294_;
}
}
}
}
v___jp_287_:
{
lean_object* v_size_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_size_290_ = lean_ctor_get(v___y_288_, 0);
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_size_290_, v___x_291_);
lean_inc(v_a_260_);
v___x_293_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_288_, v___x_292_, v_i_289_, v_a_260_, v___x_286_);
lean_dec(v_i_289_);
v___y_276_ = v___x_293_;
goto v___jp_275_;
}
v___jp_294_:
{
lean_object* v___x_296_; 
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v___y_295_, v_a_260_);
switch(lean_obj_tag(v___x_296_))
{
case 0:
{
lean_object* v_index_297_; lean_object* v_size_298_; lean_object* v___x_299_; 
v_index_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_index_297_);
lean_dec_ref_known(v___x_296_, 3);
v_size_298_ = lean_ctor_get(v___y_295_, 0);
lean_inc(v_size_298_);
lean_inc(v_a_260_);
v___x_299_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_295_, v_size_298_, v_index_297_, v_a_260_, v___x_286_);
lean_dec(v_index_297_);
v___y_276_ = v___x_299_;
goto v___jp_275_;
}
case 1:
{
lean_object* v_index_300_; 
v_index_300_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_index_300_);
lean_dec_ref_known(v___x_296_, 1);
v___y_288_ = v___y_295_;
v_i_289_ = v_index_300_;
goto v___jp_287_;
}
default: 
{
lean_object* v___x_301_; 
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_295_, v___x_259_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_index_302_; 
v_index_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_index_302_);
lean_dec_ref_known(v___x_301_, 1);
v___y_288_ = v___y_295_;
v_i_289_ = v_index_302_;
goto v___jp_287_;
}
else
{
v___y_276_ = v___y_295_;
goto v___jp_275_;
}
}
}
}
v___jp_303_:
{
lean_object* v_size_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_size_306_ = lean_ctor_get(v___y_304_, 0);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_size_306_, v___x_307_);
lean_inc(v_a_260_);
v___x_309_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_304_, v___x_308_, v_i_305_, v_a_260_, v___x_286_);
lean_dec(v_i_305_);
v___y_276_ = v___x_309_;
goto v___jp_275_;
}
v___jp_310_:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___redArg(v_snd_271_);
lean_dec(v_snd_271_);
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v___x_311_, v_a_260_);
switch(lean_obj_tag(v___x_312_))
{
case 0:
{
lean_object* v_index_313_; lean_object* v_size_314_; lean_object* v___x_315_; 
v_index_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_index_313_);
lean_dec_ref_known(v___x_312_, 3);
v_size_314_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_size_314_);
lean_inc(v_a_260_);
v___x_315_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_311_, v_size_314_, v_index_313_, v_a_260_, v___x_286_);
lean_dec(v_index_313_);
v___y_276_ = v___x_315_;
goto v___jp_275_;
}
case 1:
{
lean_object* v_index_316_; 
v_index_316_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_index_316_);
lean_dec_ref_known(v___x_312_, 1);
v___y_304_ = v___x_311_;
v_i_305_ = v_index_316_;
goto v___jp_303_;
}
default: 
{
lean_object* v___x_317_; 
v___x_317_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_311_, v___x_259_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_index_318_; 
v_index_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_index_318_);
lean_dec_ref_known(v___x_317_, 1);
v___y_304_ = v___x_311_;
v_i_305_ = v_index_318_;
goto v___jp_303_;
}
else
{
v___y_276_ = v___x_311_;
goto v___jp_275_;
}
}
}
}
}
v___jp_275_:
{
lean_object* v___x_278_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 1, v___y_276_);
v___x_278_ = v___x_273_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_fst_270_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___y_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
v_a_251_ = v___x_278_;
goto v___jp_250_;
}
}
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec_ref(v_b_240_);
v_a_348_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_263_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_263_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec_ref(v_b_240_);
v_a_356_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_258_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_258_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
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
v___jp_250_:
{
size_t v___x_252_; size_t v___x_253_; 
v___x_252_ = ((size_t)1ULL);
v___x_253_ = lean_usize_add(v_i_239_, v___x_252_);
v_i_239_ = v___x_253_;
v_b_240_ = v_a_251_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___boxed(lean_object* v_as_364_, lean_object* v_sz_365_, lean_object* v_i_366_, lean_object* v_b_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
size_t v_sz_boxed_377_; size_t v_i_boxed_378_; lean_object* v_res_379_; 
v_sz_boxed_377_ = lean_unbox_usize(v_sz_365_);
lean_dec(v_sz_365_);
v_i_boxed_378_ = lean_unbox_usize(v_i_366_);
lean_dec(v_i_366_);
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(v_as_364_, v_sz_boxed_377_, v_i_boxed_378_, v_b_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec_ref(v_as_364_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4_spec__6(lean_object* v_msgData_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; lean_object* v_env_387_; lean_object* v___x_388_; lean_object* v_mctx_389_; lean_object* v_lctx_390_; lean_object* v_options_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_386_ = lean_st_ref_get(v___y_384_);
v_env_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc_ref(v_env_387_);
lean_dec(v___x_386_);
v___x_388_ = lean_st_ref_get(v___y_382_);
v_mctx_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc_ref(v_mctx_389_);
lean_dec(v___x_388_);
v_lctx_390_ = lean_ctor_get(v___y_381_, 2);
v_options_391_ = lean_ctor_get(v___y_383_, 2);
lean_inc_ref(v_options_391_);
lean_inc_ref(v_lctx_390_);
v___x_392_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_392_, 0, v_env_387_);
lean_ctor_set(v___x_392_, 1, v_mctx_389_);
lean_ctor_set(v___x_392_, 2, v_lctx_390_);
lean_ctor_set(v___x_392_, 3, v_options_391_);
v___x_393_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v_msgData_380_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4_spec__6___boxed(lean_object* v_msgData_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4_spec__6(v_msgData_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(lean_object* v_msg_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_ref_408_; lean_object* v___x_409_; lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_418_; 
v_ref_408_ = lean_ctor_get(v___y_405_, 5);
v___x_409_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4_spec__6(v_msg_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_418_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_418_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_418_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
lean_inc(v_ref_408_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v_ref_408_);
lean_ctor_set(v___x_414_, 1, v_a_410_);
if (v_isShared_413_ == 0)
{
lean_ctor_set_tag(v___x_412_, 1);
lean_ctor_set(v___x_412_, 0, v___x_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg___boxed(lean_object* v_msg_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_msg_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(lean_object* v_a_426_, lean_object* v_b_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_array_435_; lean_object* v_start_436_; lean_object* v_stop_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_452_; 
v_array_435_ = lean_ctor_get(v_a_426_, 0);
v_start_436_ = lean_ctor_get(v_a_426_, 1);
v_stop_437_ = lean_ctor_get(v_a_426_, 2);
v_isSharedCheck_452_ = !lean_is_exclusive(v_a_426_);
if (v_isSharedCheck_452_ == 0)
{
v___x_439_ = v_a_426_;
v_isShared_440_ = v_isSharedCheck_452_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_stop_437_);
lean_inc(v_start_436_);
lean_inc(v_array_435_);
lean_dec(v_a_426_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_452_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
uint8_t v___x_441_; 
v___x_441_ = lean_nat_dec_lt(v_start_436_, v_stop_437_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
lean_del_object(v___x_439_);
lean_dec(v_stop_437_);
lean_dec(v_start_436_);
lean_dec_ref(v_array_435_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v_b_427_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_array_fget_borrowed(v_array_435_, v_start_436_);
lean_inc(v___x_443_);
v___x_444_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_b_427_, v___x_443_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v_start_436_, v___x_446_);
lean_dec(v_start_436_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_447_);
v___x_449_ = v___x_439_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_array_435_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_stop_437_);
v___x_449_ = v_reuseFailAlloc_451_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
v_a_426_ = v___x_449_;
v_b_427_ = v_a_445_;
goto _start;
}
}
else
{
lean_del_object(v___x_439_);
lean_dec(v_stop_437_);
lean_dec(v_start_436_);
lean_dec_ref(v_array_435_);
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg___boxed(lean_object* v_a_453_, lean_object* v_b_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_a_453_, v_b_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_462_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__1));
v___x_467_ = l_Lean_MessageData_ofFormat(v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(lean_object* v_sats_468_, lean_object* v_unusedHypotheses_469_, lean_object* v___x_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; size_t v_sz_481_; size_t v___x_482_; lean_object* v___x_483_; 
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v_sats_468_);
lean_ctor_set(v___x_480_, 1, v_unusedHypotheses_469_);
v_sz_481_ = lean_array_size(v___y_471_);
v___x_482_ = ((size_t)0ULL);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2(v___y_471_, v_sz_481_, v___x_482_, v___x_480_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v_fst_485_; lean_object* v_snd_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v___x_483_, 1);
v_fst_485_ = lean_ctor_get(v_a_484_, 0);
lean_inc(v_fst_485_);
v_snd_486_ = lean_ctor_get(v_a_484_, 1);
lean_inc(v_snd_486_);
lean_dec(v_a_484_);
v___x_487_ = lean_array_get_size(v_fst_485_);
v___x_488_ = lean_nat_dec_eq(v___x_487_, v___x_470_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_489_ = lean_array_fget(v_fst_485_, v___x_470_);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = l_Array_toSubarray___redArg(v_fst_485_, v___x_490_, v___x_487_);
v___x_492_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v___x_491_, v___x_489_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_505_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_505_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_505_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_505_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v_bvExpr_497_; lean_object* v_expr_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v_bvExpr_497_ = lean_ctor_get(v_a_493_, 0);
v_expr_498_ = lean_ctor_get(v_a_493_, 2);
lean_inc_ref(v_expr_498_);
lean_inc_ref(v_bvExpr_497_);
v___x_499_ = l_Lean_ShareCommon_shareCommon___redArg(v_bvExpr_497_);
v___x_500_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed), 11, 1);
lean_closure_set(v___x_500_, 0, v_a_493_);
v___x_501_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
lean_ctor_set(v___x_501_, 2, v_snd_486_);
lean_ctor_set(v___x_501_, 3, v_expr_498_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_501_);
v___x_503_ = v___x_495_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec(v_snd_486_);
v_a_506_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_492_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_492_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v_snd_486_);
lean_dec(v_fst_485_);
v___x_514_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___closed__2);
v___x_515_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v___x_514_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_515_;
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
v_a_516_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_483_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_483_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed(lean_object* v_sats_524_, lean_object* v_unusedHypotheses_525_, lean_object* v___x_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0(v_sats_524_, v_unusedHypotheses_525_, v___x_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___x_526_);
return v_res_536_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0(void){
_start:
{
lean_object* v_cellCount_537_; lean_object* v___x_538_; 
v_cellCount_537_ = lean_unsigned_to_nat(16u);
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_537_);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1(void){
_start:
{
lean_object* v_cellCount_539_; lean_object* v___x_540_; 
v_cellCount_539_ = lean_unsigned_to_nat(16u);
v___x_540_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_539_);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_unusedHypotheses_544_; 
v___x_541_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__1);
v___x_542_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__0);
v___x_543_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_unusedHypotheses_544_, 0, v___x_543_);
lean_ctor_set(v_unusedHypotheses_544_, 1, v___x_542_);
lean_ctor_set(v_unusedHypotheses_544_, 2, v___x_541_);
return v_unusedHypotheses_544_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__3(void){
_start:
{
lean_object* v___x_545_; lean_object* v_unusedHypotheses_546_; lean_object* v_sats_547_; lean_object* v___f_548_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v_unusedHypotheses_546_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__2);
v_sats_547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__2___closed__1));
v___f_548_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_reflectBV___lam__0___boxed), 12, 3);
lean_closure_set(v___f_548_, 0, v_sats_547_);
lean_closure_set(v___f_548_, 1, v_unusedHypotheses_546_);
lean_closure_set(v___f_548_, 2, v___x_545_);
return v___f_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV(lean_object* v_g_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v___f_559_; lean_object* v___x_560_; 
v___f_559_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__3, &l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_reflectBV___closed__3);
v___x_560_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg(v_g_549_, v___f_559_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_reflectBV___boxed(lean_object* v_g_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0(lean_object* v_00_u03b2_572_, lean_object* v_m_573_, lean_object* v_query_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___redArg(v_m_573_, v_query_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0___boxed(lean_object* v_00_u03b2_576_, lean_object* v_m_577_, lean_object* v_query_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0(v_00_u03b2_576_, v_m_577_, v_query_578_);
lean_dec_ref(v_query_578_);
lean_dec_ref(v_m_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(lean_object* v_00_u03b2_580_, lean_object* v_m_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___redArg(v_m_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1___boxed(lean_object* v_00_u03b2_583_, lean_object* v_m_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1(v_00_u03b2_583_, v_m_584_);
lean_dec_ref(v_m_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(lean_object* v_inst_586_, lean_object* v_R_587_, lean_object* v_a_588_, lean_object* v_b_589_, lean_object* v_c_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___redArg(v_a_588_, v_b_589_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3___boxed(lean_object* v_inst_601_, lean_object* v_R_602_, lean_object* v_a_603_, lean_object* v_b_604_, lean_object* v_c_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__3(v_inst_601_, v_R_602_, v_a_603_, v_b_604_, v_c_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(lean_object* v_00_u03b1_616_, lean_object* v_msg_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___redArg(v_msg_617_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4___boxed(lean_object* v_00_u03b1_628_, lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4(v_00_u03b1_628_, v_msg_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(lean_object* v_00_u03b2_640_, lean_object* v_m_641_, lean_object* v_query_642_, lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___redArg(v_m_641_, v_query_642_, v_x_643_, v_x_644_, v_x_645_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0___boxed(lean_object* v_00_u03b2_648_, lean_object* v_m_649_, lean_object* v_query_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__0_spec__0(v_00_u03b2_648_, v_m_649_, v_query_650_, v_x_651_, v_x_652_, v_x_653_, v_x_654_);
lean_dec_ref(v_query_650_);
lean_dec_ref(v_m_649_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2(lean_object* v_00_u03b2_656_, lean_object* v_init_657_, lean_object* v_b_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2___redArg(v_init_657_, v_b_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2___boxed(lean_object* v_00_u03b2_660_, lean_object* v_init_661_, lean_object* v_b_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2(v_00_u03b2_660_, v_init_661_, v_b_662_);
lean_dec_ref(v_b_662_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_664_, lean_object* v_b_665_, lean_object* v_acc_666_, lean_object* v_i_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2_spec__4___redArg(v_b_665_, v_acc_666_, v_i_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_669_, lean_object* v_b_670_, lean_object* v_acc_671_, lean_object* v_i_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__1_spec__2_spec__4(v_00_u03b2_669_, v_b_670_, v_acc_671_, v_i_672_);
lean_dec_ref(v_b_670_);
return v_res_673_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_unsigned_to_nat(32u);
v___x_675_ = lean_mk_empty_array_with_capacity(v___x_674_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_677_ = ((size_t)5ULL);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_unsigned_to_nat(32u);
v___x_680_ = lean_mk_empty_array_with_capacity(v___x_679_);
v___x_681_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__0);
v___x_682_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v___x_680_);
lean_ctor_set(v___x_682_, 2, v___x_678_);
lean_ctor_set(v___x_682_, 3, v___x_678_);
lean_ctor_set_usize(v___x_682_, 4, v___x_677_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; lean_object* v_traceState_686_; lean_object* v_traces_687_; lean_object* v___x_688_; lean_object* v_traceState_689_; lean_object* v_env_690_; lean_object* v_nextMacroScope_691_; lean_object* v_ngen_692_; lean_object* v_auxDeclNGen_693_; lean_object* v_cache_694_; lean_object* v_messages_695_; lean_object* v_infoState_696_; lean_object* v_snapshotTasks_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_716_; 
v___x_685_ = lean_st_ref_get(v___y_683_);
v_traceState_686_ = lean_ctor_get(v___x_685_, 4);
lean_inc_ref(v_traceState_686_);
lean_dec(v___x_685_);
v_traces_687_ = lean_ctor_get(v_traceState_686_, 0);
lean_inc_ref(v_traces_687_);
lean_dec_ref(v_traceState_686_);
v___x_688_ = lean_st_ref_take(v___y_683_);
v_traceState_689_ = lean_ctor_get(v___x_688_, 4);
v_env_690_ = lean_ctor_get(v___x_688_, 0);
v_nextMacroScope_691_ = lean_ctor_get(v___x_688_, 1);
v_ngen_692_ = lean_ctor_get(v___x_688_, 2);
v_auxDeclNGen_693_ = lean_ctor_get(v___x_688_, 3);
v_cache_694_ = lean_ctor_get(v___x_688_, 5);
v_messages_695_ = lean_ctor_get(v___x_688_, 6);
v_infoState_696_ = lean_ctor_get(v___x_688_, 7);
v_snapshotTasks_697_ = lean_ctor_get(v___x_688_, 8);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_716_ == 0)
{
v___x_699_ = v___x_688_;
v_isShared_700_ = v_isSharedCheck_716_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_snapshotTasks_697_);
lean_inc(v_infoState_696_);
lean_inc(v_messages_695_);
lean_inc(v_cache_694_);
lean_inc(v_traceState_689_);
lean_inc(v_auxDeclNGen_693_);
lean_inc(v_ngen_692_);
lean_inc(v_nextMacroScope_691_);
lean_inc(v_env_690_);
lean_dec(v___x_688_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_716_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
uint64_t v_tid_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_714_; 
v_tid_701_ = lean_ctor_get_uint64(v_traceState_689_, sizeof(void*)*1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_traceState_689_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v_traceState_689_, 0);
lean_dec(v_unused_715_);
v___x_703_ = v_traceState_689_;
v_isShared_704_ = v_isSharedCheck_714_;
goto v_resetjp_702_;
}
else
{
lean_dec(v_traceState_689_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_714_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_705_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___closed__1);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_705_);
v___x_707_ = v___x_703_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_705_);
lean_ctor_set_uint64(v_reuseFailAlloc_713_, sizeof(void*)*1, v_tid_701_);
v___x_707_ = v_reuseFailAlloc_713_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 4, v___x_707_);
v___x_709_ = v___x_699_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_env_690_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_nextMacroScope_691_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_ngen_692_);
lean_ctor_set(v_reuseFailAlloc_712_, 3, v_auxDeclNGen_693_);
lean_ctor_set(v_reuseFailAlloc_712_, 4, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_712_, 5, v_cache_694_);
lean_ctor_set(v_reuseFailAlloc_712_, 6, v_messages_695_);
lean_ctor_set(v_reuseFailAlloc_712_, 7, v_infoState_696_);
lean_ctor_set(v_reuseFailAlloc_712_, 8, v_snapshotTasks_697_);
v___x_709_ = v_reuseFailAlloc_712_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_st_ref_put(v___y_683_, v___x_709_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v_traces_687_);
return v___x_711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg___boxed(lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(v___y_717_);
lean_dec(v___y_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6(lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(v___y_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___boxed(lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6(v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
return v_res_739_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(lean_object* v_opts_740_, lean_object* v_opt_741_){
_start:
{
lean_object* v_name_742_; lean_object* v_defValue_743_; lean_object* v_map_744_; lean_object* v___x_745_; 
v_name_742_ = lean_ctor_get(v_opt_741_, 0);
v_defValue_743_ = lean_ctor_get(v_opt_741_, 1);
v_map_744_ = lean_ctor_get(v_opts_740_, 0);
v___x_745_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_744_, v_name_742_);
if (lean_obj_tag(v___x_745_) == 0)
{
uint8_t v___x_746_; 
v___x_746_ = lean_unbox(v_defValue_743_);
return v___x_746_;
}
else
{
lean_object* v_val_747_; 
v_val_747_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_val_747_);
lean_dec_ref_known(v___x_745_, 1);
if (lean_obj_tag(v_val_747_) == 1)
{
uint8_t v_v_748_; 
v_v_748_ = lean_ctor_get_uint8(v_val_747_, 0);
lean_dec_ref_known(v_val_747_, 0);
return v_v_748_;
}
else
{
uint8_t v___x_749_; 
lean_dec(v_val_747_);
v___x_749_ = lean_unbox(v_defValue_743_);
return v___x_749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7___boxed(lean_object* v_opts_750_, lean_object* v_opt_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(v_opts_750_, v_opt_751_);
lean_dec_ref(v_opt_751_);
lean_dec_ref(v_opts_750_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__1));
v___x_758_ = l_Lean_MessageData_ofFormat(v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(lean_object* v_x_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___closed__2);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0___boxed(lean_object* v_x_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__0(v_x_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec_ref(v_x_771_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(lean_object* v_x_789_){
_start:
{
switch(lean_obj_tag(v_x_789_))
{
case 0:
{
lean_object* v_a_790_; lean_object* v___x_791_; 
v_a_790_ = lean_ctor_get(v_x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v_x_789_, 1);
v___x_791_ = l_Std_Tactic_BVDecide_BVPred_toString(v_a_790_);
return v___x_791_;
}
case 1:
{
uint8_t v_a_792_; 
v_a_792_ = lean_ctor_get_uint8(v_x_789_, 0);
lean_dec_ref_known(v_x_789_, 0);
if (v_a_792_ == 0)
{
lean_object* v___x_793_; 
v___x_793_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__0));
return v___x_793_;
}
else
{
lean_object* v___x_794_; 
v___x_794_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__1));
return v___x_794_;
}
}
case 2:
{
lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_a_795_ = lean_ctor_get(v_x_789_, 0);
lean_inc_ref(v_a_795_);
lean_dec_ref_known(v_x_789_, 1);
v___x_796_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__2));
v___x_797_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_a_795_);
v___x_798_ = lean_string_append(v___x_796_, v___x_797_);
lean_dec_ref(v___x_797_);
return v___x_798_;
}
case 3:
{
uint8_t v_a_799_; lean_object* v_a_800_; lean_object* v_a_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_a_799_ = lean_ctor_get_uint8(v_x_789_, sizeof(void*)*2);
v_a_800_ = lean_ctor_get(v_x_789_, 0);
lean_inc_ref(v_a_800_);
v_a_801_ = lean_ctor_get(v_x_789_, 1);
lean_inc_ref(v_a_801_);
lean_dec_ref_known(v_x_789_, 2);
v___x_802_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__3));
v___x_803_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_a_800_);
v___x_804_ = lean_string_append(v___x_802_, v___x_803_);
lean_dec_ref(v___x_803_);
v___x_805_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__4));
v___x_806_ = lean_string_append(v___x_804_, v___x_805_);
v___x_807_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_799_);
v___x_808_ = lean_string_append(v___x_806_, v___x_807_);
lean_dec_ref(v___x_807_);
v___x_809_ = lean_string_append(v___x_808_, v___x_805_);
v___x_810_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_a_801_);
v___x_811_ = lean_string_append(v___x_809_, v___x_810_);
lean_dec_ref(v___x_810_);
v___x_812_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__5));
v___x_813_ = lean_string_append(v___x_811_, v___x_812_);
return v___x_813_;
}
default: 
{
lean_object* v_a_814_; lean_object* v_a_815_; lean_object* v_a_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_a_814_ = lean_ctor_get(v_x_789_, 0);
lean_inc_ref(v_a_814_);
v_a_815_ = lean_ctor_get(v_x_789_, 1);
lean_inc_ref(v_a_815_);
v_a_816_ = lean_ctor_get(v_x_789_, 2);
lean_inc_ref(v_a_816_);
lean_dec_ref_known(v_x_789_, 3);
v___x_817_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__6));
v___x_818_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_a_814_);
v___x_819_ = lean_string_append(v___x_817_, v___x_818_);
lean_dec_ref(v___x_818_);
v___x_820_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__4));
v___x_821_ = lean_string_append(v___x_819_, v___x_820_);
v___x_822_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_a_815_);
v___x_823_ = lean_string_append(v___x_821_, v___x_822_);
lean_dec_ref(v___x_822_);
v___x_824_ = lean_string_append(v___x_823_, v___x_820_);
v___x_825_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_a_816_);
v___x_826_ = lean_string_append(v___x_824_, v___x_825_);
lean_dec_ref(v___x_825_);
v___x_827_ = ((lean_object*)(l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4___closed__5));
v___x_828_ = lean_string_append(v___x_826_, v___x_827_);
return v___x_828_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_829_; double v___x_830_; 
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_float_of_nat(v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(lean_object* v_cls_834_, lean_object* v_msg_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_ref_841_; lean_object* v___x_842_; lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_887_; 
v_ref_841_ = lean_ctor_get(v___y_838_, 5);
v___x_842_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4_spec__6(v_msg_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_887_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_887_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_887_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v_traceState_848_; lean_object* v_env_849_; lean_object* v_nextMacroScope_850_; lean_object* v_ngen_851_; lean_object* v_auxDeclNGen_852_; lean_object* v_cache_853_; lean_object* v_messages_854_; lean_object* v_infoState_855_; lean_object* v_snapshotTasks_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_886_; 
v___x_847_ = lean_st_ref_take(v___y_839_);
v_traceState_848_ = lean_ctor_get(v___x_847_, 4);
v_env_849_ = lean_ctor_get(v___x_847_, 0);
v_nextMacroScope_850_ = lean_ctor_get(v___x_847_, 1);
v_ngen_851_ = lean_ctor_get(v___x_847_, 2);
v_auxDeclNGen_852_ = lean_ctor_get(v___x_847_, 3);
v_cache_853_ = lean_ctor_get(v___x_847_, 5);
v_messages_854_ = lean_ctor_get(v___x_847_, 6);
v_infoState_855_ = lean_ctor_get(v___x_847_, 7);
v_snapshotTasks_856_ = lean_ctor_get(v___x_847_, 8);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_886_ == 0)
{
v___x_858_ = v___x_847_;
v_isShared_859_ = v_isSharedCheck_886_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_snapshotTasks_856_);
lean_inc(v_infoState_855_);
lean_inc(v_messages_854_);
lean_inc(v_cache_853_);
lean_inc(v_traceState_848_);
lean_inc(v_auxDeclNGen_852_);
lean_inc(v_ngen_851_);
lean_inc(v_nextMacroScope_850_);
lean_inc(v_env_849_);
lean_dec(v___x_847_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_886_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
uint64_t v_tid_860_; lean_object* v_traces_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_885_; 
v_tid_860_ = lean_ctor_get_uint64(v_traceState_848_, sizeof(void*)*1);
v_traces_861_ = lean_ctor_get(v_traceState_848_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v_traceState_848_);
if (v_isSharedCheck_885_ == 0)
{
v___x_863_ = v_traceState_848_;
v_isShared_864_ = v_isSharedCheck_885_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_traces_861_);
lean_dec(v_traceState_848_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_885_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; double v___x_866_; uint8_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_865_ = lean_box(0);
v___x_866_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__0);
v___x_867_ = 0;
v___x_868_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__1));
v___x_869_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_869_, 0, v_cls_834_);
lean_ctor_set(v___x_869_, 1, v___x_865_);
lean_ctor_set(v___x_869_, 2, v___x_868_);
lean_ctor_set_float(v___x_869_, sizeof(void*)*3, v___x_866_);
lean_ctor_set_float(v___x_869_, sizeof(void*)*3 + 8, v___x_866_);
lean_ctor_set_uint8(v___x_869_, sizeof(void*)*3 + 16, v___x_867_);
v___x_870_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__2));
v___x_871_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v_a_843_);
lean_ctor_set(v___x_871_, 2, v___x_870_);
lean_inc(v_ref_841_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_ref_841_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = l_Lean_PersistentArray_push___redArg(v_traces_861_, v___x_872_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_873_);
v___x_875_ = v___x_863_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_873_);
lean_ctor_set_uint64(v_reuseFailAlloc_884_, sizeof(void*)*1, v_tid_860_);
v___x_875_ = v_reuseFailAlloc_884_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 4, v___x_875_);
v___x_877_ = v___x_858_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_env_849_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_nextMacroScope_850_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v_ngen_851_);
lean_ctor_set(v_reuseFailAlloc_883_, 3, v_auxDeclNGen_852_);
lean_ctor_set(v_reuseFailAlloc_883_, 4, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_883_, 5, v_cache_853_);
lean_ctor_set(v_reuseFailAlloc_883_, 6, v_messages_854_);
lean_ctor_set(v_reuseFailAlloc_883_, 7, v_infoState_855_);
lean_ctor_set(v_reuseFailAlloc_883_, 8, v_snapshotTasks_856_);
v___x_877_ = v_reuseFailAlloc_883_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_878_ = lean_st_ref_put(v___y_839_, v___x_877_);
v___x_879_ = lean_box(0);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_879_);
v___x_881_ = v___x_845_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___boxed(lean_object* v_cls_888_, lean_object* v_msg_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(v_cls_888_, v_msg_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(lean_object* v_b_896_, lean_object* v_acc_897_, lean_object* v_i_898_){
_start:
{
lean_object* v_keyArray_903_; lean_object* v_valueArray_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v_keyArray_903_ = lean_ctor_get(v_b_896_, 1);
v_valueArray_904_ = lean_ctor_get(v_b_896_, 2);
v___x_905_ = lean_array_get_size(v_keyArray_903_);
v___x_906_ = lean_nat_dec_lt(v_i_898_, v___x_905_);
if (v___x_906_ == 0)
{
lean_dec(v_i_898_);
lean_inc(v_acc_897_);
return v_acc_897_;
}
else
{
lean_object* v___x_907_; uint8_t v_isSome_908_; 
v___x_907_ = lean_array_fget_borrowed(v_keyArray_903_, v_i_898_);
v_isSome_908_ = lean_noption_is_some(v___x_907_);
if (v_isSome_908_ == 0)
{
goto v___jp_899_;
}
else
{
lean_object* v___x_909_; uint8_t v_isSome_910_; 
v___x_909_ = lean_array_fget_borrowed(v_valueArray_904_, v_i_898_);
v_isSome_910_ = lean_noption_is_some(v___x_909_);
if (v_isSome_910_ == 0)
{
goto v___jp_899_;
}
else
{
lean_object* v_val_911_; lean_object* v_val_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_inc(v___x_907_);
v_val_911_ = lean_noption_get(v___x_907_);
lean_inc(v___x_909_);
v_val_912_ = lean_noption_get(v___x_909_);
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = lean_nat_add(v_i_898_, v___x_913_);
lean_dec(v_i_898_);
v___x_915_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_b_896_, v_acc_897_, v___x_914_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v_val_911_);
lean_ctor_set(v___x_916_, 1, v_val_912_);
v___x_917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___x_915_);
return v___x_917_;
}
}
}
v___jp_899_:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_unsigned_to_nat(1u);
v___x_901_ = lean_nat_add(v_i_898_, v___x_900_);
lean_dec(v_i_898_);
v_i_898_ = v___x_901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0___boxed(lean_object* v_b_918_, lean_object* v_acc_919_, lean_object* v_i_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_b_918_, v_acc_919_, v_i_920_);
lean_dec(v_acc_919_);
lean_dec_ref(v_b_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
if (lean_obj_tag(v_a_922_) == 0)
{
lean_object* v___x_924_; 
v___x_924_ = l_List_reverse___redArg(v_a_923_);
return v___x_924_;
}
else
{
lean_object* v_head_925_; lean_object* v_snd_926_; lean_object* v_tail_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_950_; 
v_head_925_ = lean_ctor_get(v_a_922_, 0);
lean_inc(v_head_925_);
v_snd_926_ = lean_ctor_get(v_head_925_, 1);
lean_inc(v_snd_926_);
v_tail_927_ = lean_ctor_get(v_a_922_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_a_922_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_a_922_, 0);
lean_dec(v_unused_951_);
v___x_929_ = v_a_922_;
v_isShared_930_ = v_isSharedCheck_950_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_tail_927_);
lean_dec(v_a_922_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_950_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_fst_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_948_; 
v_fst_931_ = lean_ctor_get(v_head_925_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_head_925_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_head_925_, 1);
lean_dec(v_unused_949_);
v___x_933_ = v_head_925_;
v_isShared_934_ = v_isSharedCheck_948_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_fst_931_);
lean_dec(v_head_925_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_948_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_width_935_; lean_object* v_atomNumber_936_; uint8_t v_synthetic_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v_width_935_ = lean_ctor_get(v_snd_926_, 0);
lean_inc(v_width_935_);
v_atomNumber_936_ = lean_ctor_get(v_snd_926_, 1);
lean_inc(v_atomNumber_936_);
v_synthetic_937_ = lean_ctor_get_uint8(v_snd_926_, sizeof(void*)*2);
lean_dec(v_snd_926_);
v___x_938_ = lean_box(v_synthetic_937_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_938_);
v___x_940_ = v___x_933_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_fst_931_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_938_);
v___x_940_ = v_reuseFailAlloc_947_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v_width_935_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v_atomNumber_936_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v_a_923_);
lean_ctor_set(v___x_929_, 0, v___x_942_);
v___x_944_ = v___x_929_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_a_923_);
v___x_944_ = v_reuseFailAlloc_946_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
v_a_922_ = v_tail_927_;
v_a_923_ = v___x_944_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12_spec__16(size_t v_sz_952_, size_t v_i_953_, lean_object* v_bs_954_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = lean_usize_dec_lt(v_i_953_, v_sz_952_);
if (v___x_955_ == 0)
{
return v_bs_954_;
}
else
{
lean_object* v_v_956_; lean_object* v_msg_957_; lean_object* v___x_958_; lean_object* v_bs_x27_959_; size_t v___x_960_; size_t v___x_961_; lean_object* v___x_962_; 
v_v_956_ = lean_array_uget_borrowed(v_bs_954_, v_i_953_);
v_msg_957_ = lean_ctor_get(v_v_956_, 1);
lean_inc_ref(v_msg_957_);
v___x_958_ = lean_unsigned_to_nat(0u);
v_bs_x27_959_ = lean_array_uset(v_bs_954_, v_i_953_, v___x_958_);
v___x_960_ = ((size_t)1ULL);
v___x_961_ = lean_usize_add(v_i_953_, v___x_960_);
v___x_962_ = lean_array_uset(v_bs_x27_959_, v_i_953_, v_msg_957_);
v_i_953_ = v___x_961_;
v_bs_954_ = v___x_962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12_spec__16___boxed(lean_object* v_sz_964_, lean_object* v_i_965_, lean_object* v_bs_966_){
_start:
{
size_t v_sz_boxed_967_; size_t v_i_boxed_968_; lean_object* v_res_969_; 
v_sz_boxed_967_ = lean_unbox_usize(v_sz_964_);
lean_dec(v_sz_964_);
v_i_boxed_968_ = lean_unbox_usize(v_i_965_);
lean_dec(v_i_965_);
v_res_969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12_spec__16(v_sz_boxed_967_, v_i_boxed_968_, v_bs_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12___redArg(lean_object* v_oldTraces_970_, lean_object* v_data_971_, lean_object* v_ref_972_, lean_object* v_msg_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_fileName_979_; lean_object* v_fileMap_980_; lean_object* v_options_981_; lean_object* v_currRecDepth_982_; lean_object* v_maxRecDepth_983_; lean_object* v_ref_984_; lean_object* v_currNamespace_985_; lean_object* v_openDecls_986_; lean_object* v_initHeartbeats_987_; lean_object* v_maxHeartbeats_988_; lean_object* v_quotContext_989_; lean_object* v_currMacroScope_990_; uint8_t v_diag_991_; lean_object* v_cancelTk_x3f_992_; uint8_t v_suppressElabErrors_993_; lean_object* v_inheritedTraceOptions_994_; lean_object* v___x_995_; lean_object* v_traceState_996_; lean_object* v_traces_997_; lean_object* v_ref_998_; lean_object* v___x_999_; lean_object* v___x_1000_; size_t v_sz_1001_; size_t v___x_1002_; lean_object* v___x_1003_; lean_object* v_msg_1004_; lean_object* v___x_1005_; lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1043_; 
v_fileName_979_ = lean_ctor_get(v___y_976_, 0);
v_fileMap_980_ = lean_ctor_get(v___y_976_, 1);
v_options_981_ = lean_ctor_get(v___y_976_, 2);
v_currRecDepth_982_ = lean_ctor_get(v___y_976_, 3);
v_maxRecDepth_983_ = lean_ctor_get(v___y_976_, 4);
v_ref_984_ = lean_ctor_get(v___y_976_, 5);
v_currNamespace_985_ = lean_ctor_get(v___y_976_, 6);
v_openDecls_986_ = lean_ctor_get(v___y_976_, 7);
v_initHeartbeats_987_ = lean_ctor_get(v___y_976_, 8);
v_maxHeartbeats_988_ = lean_ctor_get(v___y_976_, 9);
v_quotContext_989_ = lean_ctor_get(v___y_976_, 10);
v_currMacroScope_990_ = lean_ctor_get(v___y_976_, 11);
v_diag_991_ = lean_ctor_get_uint8(v___y_976_, sizeof(void*)*14);
v_cancelTk_x3f_992_ = lean_ctor_get(v___y_976_, 12);
v_suppressElabErrors_993_ = lean_ctor_get_uint8(v___y_976_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_994_ = lean_ctor_get(v___y_976_, 13);
v___x_995_ = lean_st_ref_get(v___y_977_);
v_traceState_996_ = lean_ctor_get(v___x_995_, 4);
lean_inc_ref(v_traceState_996_);
lean_dec(v___x_995_);
v_traces_997_ = lean_ctor_get(v_traceState_996_, 0);
lean_inc_ref(v_traces_997_);
lean_dec_ref(v_traceState_996_);
v_ref_998_ = l_Lean_replaceRef(v_ref_972_, v_ref_984_);
lean_inc_ref(v_inheritedTraceOptions_994_);
lean_inc(v_cancelTk_x3f_992_);
lean_inc(v_currMacroScope_990_);
lean_inc(v_quotContext_989_);
lean_inc(v_maxHeartbeats_988_);
lean_inc(v_initHeartbeats_987_);
lean_inc(v_openDecls_986_);
lean_inc(v_currNamespace_985_);
lean_inc(v_maxRecDepth_983_);
lean_inc(v_currRecDepth_982_);
lean_inc_ref(v_options_981_);
lean_inc_ref(v_fileMap_980_);
lean_inc_ref(v_fileName_979_);
v___x_999_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_999_, 0, v_fileName_979_);
lean_ctor_set(v___x_999_, 1, v_fileMap_980_);
lean_ctor_set(v___x_999_, 2, v_options_981_);
lean_ctor_set(v___x_999_, 3, v_currRecDepth_982_);
lean_ctor_set(v___x_999_, 4, v_maxRecDepth_983_);
lean_ctor_set(v___x_999_, 5, v_ref_998_);
lean_ctor_set(v___x_999_, 6, v_currNamespace_985_);
lean_ctor_set(v___x_999_, 7, v_openDecls_986_);
lean_ctor_set(v___x_999_, 8, v_initHeartbeats_987_);
lean_ctor_set(v___x_999_, 9, v_maxHeartbeats_988_);
lean_ctor_set(v___x_999_, 10, v_quotContext_989_);
lean_ctor_set(v___x_999_, 11, v_currMacroScope_990_);
lean_ctor_set(v___x_999_, 12, v_cancelTk_x3f_992_);
lean_ctor_set(v___x_999_, 13, v_inheritedTraceOptions_994_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*14, v_diag_991_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*14 + 1, v_suppressElabErrors_993_);
v___x_1000_ = l_Lean_PersistentArray_toArray___redArg(v_traces_997_);
lean_dec_ref(v_traces_997_);
v_sz_1001_ = lean_array_size(v___x_1000_);
v___x_1002_ = ((size_t)0ULL);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12_spec__16(v_sz_1001_, v___x_1002_, v___x_1000_);
v_msg_1004_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1004_, 0, v_data_971_);
lean_ctor_set(v_msg_1004_, 1, v_msg_973_);
lean_ctor_set(v_msg_1004_, 2, v___x_1003_);
v___x_1005_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__4_spec__6(v_msg_1004_, v___y_974_, v___y_975_, v___x_999_, v___y_977_);
lean_dec_ref_known(v___x_999_, 14);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1043_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1043_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v_traceState_1011_; lean_object* v_env_1012_; lean_object* v_nextMacroScope_1013_; lean_object* v_ngen_1014_; lean_object* v_auxDeclNGen_1015_; lean_object* v_cache_1016_; lean_object* v_messages_1017_; lean_object* v_infoState_1018_; lean_object* v_snapshotTasks_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1042_; 
v___x_1010_ = lean_st_ref_take(v___y_977_);
v_traceState_1011_ = lean_ctor_get(v___x_1010_, 4);
v_env_1012_ = lean_ctor_get(v___x_1010_, 0);
v_nextMacroScope_1013_ = lean_ctor_get(v___x_1010_, 1);
v_ngen_1014_ = lean_ctor_get(v___x_1010_, 2);
v_auxDeclNGen_1015_ = lean_ctor_get(v___x_1010_, 3);
v_cache_1016_ = lean_ctor_get(v___x_1010_, 5);
v_messages_1017_ = lean_ctor_get(v___x_1010_, 6);
v_infoState_1018_ = lean_ctor_get(v___x_1010_, 7);
v_snapshotTasks_1019_ = lean_ctor_get(v___x_1010_, 8);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1021_ = v___x_1010_;
v_isShared_1022_ = v_isSharedCheck_1042_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_snapshotTasks_1019_);
lean_inc(v_infoState_1018_);
lean_inc(v_messages_1017_);
lean_inc(v_cache_1016_);
lean_inc(v_traceState_1011_);
lean_inc(v_auxDeclNGen_1015_);
lean_inc(v_ngen_1014_);
lean_inc(v_nextMacroScope_1013_);
lean_inc(v_env_1012_);
lean_dec(v___x_1010_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1042_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
uint64_t v_tid_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1040_; 
v_tid_1023_ = lean_ctor_get_uint64(v_traceState_1011_, sizeof(void*)*1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_traceState_1011_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v_traceState_1011_, 0);
lean_dec(v_unused_1041_);
v___x_1025_ = v_traceState_1011_;
v_isShared_1026_ = v_isSharedCheck_1040_;
goto v_resetjp_1024_;
}
else
{
lean_dec(v_traceState_1011_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1040_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_ref_972_);
lean_ctor_set(v___x_1027_, 1, v_a_1006_);
v___x_1028_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_970_, v___x_1027_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1028_);
v___x_1030_ = v___x_1025_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1028_);
lean_ctor_set_uint64(v_reuseFailAlloc_1039_, sizeof(void*)*1, v_tid_1023_);
v___x_1030_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 4, v___x_1030_);
v___x_1032_ = v___x_1021_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_env_1012_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_nextMacroScope_1013_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_ngen_1014_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v_auxDeclNGen_1015_);
lean_ctor_set(v_reuseFailAlloc_1038_, 4, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1038_, 5, v_cache_1016_);
lean_ctor_set(v_reuseFailAlloc_1038_, 6, v_messages_1017_);
lean_ctor_set(v_reuseFailAlloc_1038_, 7, v_infoState_1018_);
lean_ctor_set(v_reuseFailAlloc_1038_, 8, v_snapshotTasks_1019_);
v___x_1032_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1033_ = lean_st_ref_put(v___y_977_, v___x_1032_);
v___x_1034_ = lean_box(0);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1034_);
v___x_1036_ = v___x_1008_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12___redArg___boxed(lean_object* v_oldTraces_1044_, lean_object* v_data_1045_, lean_object* v_ref_1046_, lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12___redArg(v_oldTraces_1044_, v_data_1045_, v_ref_1046_, v_msg_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__13___redArg(lean_object* v_x_1054_){
_start:
{
if (lean_obj_tag(v_x_1054_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v_x_1054_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_x_1054_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v_x_1054_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v_x_1054_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 1);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v_x_1054_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_x_1054_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v_x_1054_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v_x_1054_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__13___redArg___boxed(lean_object* v_x_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__13___redArg(v_x_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__14(lean_object* v_e_1075_){
_start:
{
if (lean_obj_tag(v_e_1075_) == 0)
{
uint8_t v___x_1076_; 
v___x_1076_ = 2;
return v___x_1076_;
}
else
{
uint8_t v___x_1077_; 
v___x_1077_ = 0;
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__14___boxed(lean_object* v_e_1078_){
_start:
{
uint8_t v_res_1079_; lean_object* v_r_1080_; 
v_res_1079_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__14(v_e_1078_);
lean_dec_ref(v_e_1078_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__15(lean_object* v_opts_1081_, lean_object* v_opt_1082_){
_start:
{
lean_object* v_name_1083_; lean_object* v_defValue_1084_; lean_object* v_map_1085_; lean_object* v___x_1086_; 
v_name_1083_ = lean_ctor_get(v_opt_1082_, 0);
v_defValue_1084_ = lean_ctor_get(v_opt_1082_, 1);
v_map_1085_ = lean_ctor_get(v_opts_1081_, 0);
v___x_1086_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1085_, v_name_1083_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_inc(v_defValue_1084_);
return v_defValue_1084_;
}
else
{
lean_object* v_val_1087_; 
v_val_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_val_1087_);
lean_dec_ref_known(v___x_1086_, 1);
if (lean_obj_tag(v_val_1087_) == 3)
{
lean_object* v_v_1088_; 
v_v_1088_ = lean_ctor_get(v_val_1087_, 0);
lean_inc(v_v_1088_);
lean_dec_ref_known(v_val_1087_, 1);
return v_v_1088_;
}
else
{
lean_dec(v_val_1087_);
lean_inc(v_defValue_1084_);
return v_defValue_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__15___boxed(lean_object* v_opts_1089_, lean_object* v_opt_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__15(v_opts_1089_, v_opt_1090_);
lean_dec_ref(v_opt_1090_);
lean_dec_ref(v_opts_1089_);
return v_res_1091_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__1(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__0));
v___x_1094_ = l_Lean_stringToMessageData(v___x_1093_);
return v___x_1094_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__2(void){
_start:
{
lean_object* v___x_1095_; double v___x_1096_; 
v___x_1095_ = lean_unsigned_to_nat(1000u);
v___x_1096_ = lean_float_of_nat(v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(lean_object* v_cls_1097_, uint8_t v_collapsed_1098_, lean_object* v_tag_1099_, lean_object* v_opts_1100_, uint8_t v_clsEnabled_1101_, lean_object* v_oldTraces_1102_, lean_object* v_msg_1103_, lean_object* v_resStartStop_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_fst_1114_; lean_object* v_snd_1115_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v_data_1119_; lean_object* v_fst_1130_; lean_object* v_snd_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; lean_object* v___y_1135_; lean_object* v_a_1136_; uint8_t v___y_1151_; double v___y_1182_; 
v_fst_1114_ = lean_ctor_get(v_resStartStop_1104_, 0);
lean_inc(v_fst_1114_);
v_snd_1115_ = lean_ctor_get(v_resStartStop_1104_, 1);
lean_inc(v_snd_1115_);
lean_dec_ref(v_resStartStop_1104_);
v_fst_1130_ = lean_ctor_get(v_snd_1115_, 0);
lean_inc(v_fst_1130_);
v_snd_1131_ = lean_ctor_get(v_snd_1115_, 1);
lean_inc(v_snd_1131_);
lean_dec(v_snd_1115_);
v___x_1132_ = l_Lean_trace_profiler;
v___x_1133_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(v_opts_1100_, v___x_1132_);
if (v___x_1133_ == 0)
{
v___y_1151_ = v___x_1133_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1188_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(v_opts_1100_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; double v___x_1191_; double v___x_1192_; double v___x_1193_; 
v___x_1189_ = l_Lean_trace_profiler_threshold;
v___x_1190_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__15(v_opts_1100_, v___x_1189_);
v___x_1191_ = lean_float_of_nat(v___x_1190_);
v___x_1192_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__2);
v___x_1193_ = lean_float_div(v___x_1191_, v___x_1192_);
v___y_1182_ = v___x_1193_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; double v___x_1196_; 
v___x_1194_ = l_Lean_trace_profiler_threshold;
v___x_1195_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__15(v_opts_1100_, v___x_1194_);
v___x_1196_ = lean_float_of_nat(v___x_1195_);
v___y_1182_ = v___x_1196_;
goto v___jp_1181_;
}
}
v___jp_1116_:
{
lean_object* v___x_1120_; 
lean_inc(v___y_1118_);
v___x_1120_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12___redArg(v_oldTraces_1102_, v_data_1119_, v___y_1118_, v___y_1117_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v___x_1121_; 
lean_dec_ref_known(v___x_1120_, 1);
v___x_1121_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__13___redArg(v_fst_1114_);
return v___x_1121_;
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v_fst_1114_);
v_a_1122_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1120_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1120_);
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
v___jp_1134_:
{
uint8_t v_result_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; double v___x_1140_; lean_object* v_data_1141_; 
v_result_1137_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__14(v_fst_1114_);
v___x_1138_ = lean_box(v_result_1137_);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
v___x_1140_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__0);
lean_inc_ref(v_tag_1099_);
lean_inc_ref(v___x_1139_);
lean_inc(v_cls_1097_);
v_data_1141_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1141_, 0, v_cls_1097_);
lean_ctor_set(v_data_1141_, 1, v___x_1139_);
lean_ctor_set(v_data_1141_, 2, v_tag_1099_);
lean_ctor_set_float(v_data_1141_, sizeof(void*)*3, v___x_1140_);
lean_ctor_set_float(v_data_1141_, sizeof(void*)*3 + 8, v___x_1140_);
lean_ctor_set_uint8(v_data_1141_, sizeof(void*)*3 + 16, v_collapsed_1098_);
if (v___x_1133_ == 0)
{
lean_dec_ref_known(v___x_1139_, 1);
lean_dec(v_snd_1131_);
lean_dec(v_fst_1130_);
lean_dec_ref(v_tag_1099_);
lean_dec(v_cls_1097_);
v___y_1117_ = v_a_1136_;
v___y_1118_ = v___y_1135_;
v_data_1119_ = v_data_1141_;
goto v___jp_1116_;
}
else
{
lean_object* v_data_1142_; double v___x_1143_; double v___x_1144_; 
lean_dec_ref_known(v_data_1141_, 3);
v_data_1142_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1142_, 0, v_cls_1097_);
lean_ctor_set(v_data_1142_, 1, v___x_1139_);
lean_ctor_set(v_data_1142_, 2, v_tag_1099_);
v___x_1143_ = lean_unbox_float(v_fst_1130_);
lean_dec(v_fst_1130_);
lean_ctor_set_float(v_data_1142_, sizeof(void*)*3, v___x_1143_);
v___x_1144_ = lean_unbox_float(v_snd_1131_);
lean_dec(v_snd_1131_);
lean_ctor_set_float(v_data_1142_, sizeof(void*)*3 + 8, v___x_1144_);
lean_ctor_set_uint8(v_data_1142_, sizeof(void*)*3 + 16, v_collapsed_1098_);
v___y_1117_ = v_a_1136_;
v___y_1118_ = v___y_1135_;
v_data_1119_ = v_data_1142_;
goto v___jp_1116_;
}
}
v___jp_1145_:
{
lean_object* v_ref_1146_; lean_object* v___x_1147_; 
v_ref_1146_ = lean_ctor_get(v___y_1111_, 5);
lean_inc(v___y_1112_);
lean_inc_ref(v___y_1111_);
lean_inc(v___y_1110_);
lean_inc_ref(v___y_1109_);
lean_inc(v___y_1108_);
lean_inc_ref(v___y_1107_);
lean_inc(v___y_1106_);
lean_inc_ref(v___y_1105_);
lean_inc(v_fst_1114_);
v___x_1147_ = lean_apply_10(v_msg_1103_, v_fst_1114_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, lean_box(0));
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v___y_1135_ = v_ref_1146_;
v_a_1136_ = v_a_1148_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1149_; 
lean_dec_ref_known(v___x_1147_, 1);
v___x_1149_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___closed__1);
v___y_1135_ = v_ref_1146_;
v_a_1136_ = v___x_1149_;
goto v___jp_1134_;
}
}
v___jp_1150_:
{
if (v_clsEnabled_1101_ == 0)
{
if (v___y_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v_traceState_1153_; lean_object* v_env_1154_; lean_object* v_nextMacroScope_1155_; lean_object* v_ngen_1156_; lean_object* v_auxDeclNGen_1157_; lean_object* v_cache_1158_; lean_object* v_messages_1159_; lean_object* v_infoState_1160_; lean_object* v_snapshotTasks_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1180_; 
lean_dec(v_snd_1131_);
lean_dec(v_fst_1130_);
lean_dec_ref(v_msg_1103_);
lean_dec_ref(v_tag_1099_);
lean_dec(v_cls_1097_);
v___x_1152_ = lean_st_ref_take(v___y_1112_);
v_traceState_1153_ = lean_ctor_get(v___x_1152_, 4);
v_env_1154_ = lean_ctor_get(v___x_1152_, 0);
v_nextMacroScope_1155_ = lean_ctor_get(v___x_1152_, 1);
v_ngen_1156_ = lean_ctor_get(v___x_1152_, 2);
v_auxDeclNGen_1157_ = lean_ctor_get(v___x_1152_, 3);
v_cache_1158_ = lean_ctor_get(v___x_1152_, 5);
v_messages_1159_ = lean_ctor_get(v___x_1152_, 6);
v_infoState_1160_ = lean_ctor_get(v___x_1152_, 7);
v_snapshotTasks_1161_ = lean_ctor_get(v___x_1152_, 8);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1163_ = v___x_1152_;
v_isShared_1164_ = v_isSharedCheck_1180_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_snapshotTasks_1161_);
lean_inc(v_infoState_1160_);
lean_inc(v_messages_1159_);
lean_inc(v_cache_1158_);
lean_inc(v_traceState_1153_);
lean_inc(v_auxDeclNGen_1157_);
lean_inc(v_ngen_1156_);
lean_inc(v_nextMacroScope_1155_);
lean_inc(v_env_1154_);
lean_dec(v___x_1152_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1180_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
uint64_t v_tid_1165_; lean_object* v_traces_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1179_; 
v_tid_1165_ = lean_ctor_get_uint64(v_traceState_1153_, sizeof(void*)*1);
v_traces_1166_ = lean_ctor_get(v_traceState_1153_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_traceState_1153_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1168_ = v_traceState_1153_;
v_isShared_1169_ = v_isSharedCheck_1179_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_traces_1166_);
lean_dec(v_traceState_1153_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1179_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1102_, v_traces_1166_);
lean_dec_ref(v_traces_1166_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1170_);
v___x_1172_ = v___x_1168_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1170_);
lean_ctor_set_uint64(v_reuseFailAlloc_1178_, sizeof(void*)*1, v_tid_1165_);
v___x_1172_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1174_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 4, v___x_1172_);
v___x_1174_ = v___x_1163_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_env_1154_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_nextMacroScope_1155_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_ngen_1156_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_auxDeclNGen_1157_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1177_, 5, v_cache_1158_);
lean_ctor_set(v_reuseFailAlloc_1177_, 6, v_messages_1159_);
lean_ctor_set(v_reuseFailAlloc_1177_, 7, v_infoState_1160_);
lean_ctor_set(v_reuseFailAlloc_1177_, 8, v_snapshotTasks_1161_);
v___x_1174_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_st_ref_put(v___y_1112_, v___x_1174_);
v___x_1176_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__13___redArg(v_fst_1114_);
return v___x_1176_;
}
}
}
}
}
else
{
goto v___jp_1145_;
}
}
else
{
goto v___jp_1145_;
}
}
v___jp_1181_:
{
double v___x_1183_; double v___x_1184_; double v___x_1185_; uint8_t v___x_1186_; 
v___x_1183_ = lean_unbox_float(v_snd_1131_);
v___x_1184_ = lean_unbox_float(v_fst_1130_);
v___x_1185_ = lean_float_sub(v___x_1183_, v___x_1184_);
v___x_1186_ = lean_float_decLt(v___y_1182_, v___x_1185_);
v___y_1151_ = v___x_1186_;
goto v___jp_1150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8___boxed(lean_object** _args){
lean_object* v_cls_1197_ = _args[0];
lean_object* v_collapsed_1198_ = _args[1];
lean_object* v_tag_1199_ = _args[2];
lean_object* v_opts_1200_ = _args[3];
lean_object* v_clsEnabled_1201_ = _args[4];
lean_object* v_oldTraces_1202_ = _args[5];
lean_object* v_msg_1203_ = _args[6];
lean_object* v_resStartStop_1204_ = _args[7];
lean_object* v___y_1205_ = _args[8];
lean_object* v___y_1206_ = _args[9];
lean_object* v___y_1207_ = _args[10];
lean_object* v___y_1208_ = _args[11];
lean_object* v___y_1209_ = _args[12];
lean_object* v___y_1210_ = _args[13];
lean_object* v___y_1211_ = _args[14];
lean_object* v___y_1212_ = _args[15];
lean_object* v___y_1213_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1214_; uint8_t v_clsEnabled_boxed_1215_; lean_object* v_res_1216_; 
v_collapsed_boxed_1214_ = lean_unbox(v_collapsed_1198_);
v_clsEnabled_boxed_1215_ = lean_unbox(v_clsEnabled_1201_);
v_res_1216_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_cls_1197_, v_collapsed_boxed_1214_, v_tag_1199_, v_opts_1200_, v_clsEnabled_boxed_1215_, v_oldTraces_1202_, v_msg_1203_, v_resStartStop_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec_ref(v_opts_1200_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__19_spec__21___redArg(lean_object* v_x_1217_, lean_object* v_x_1218_, lean_object* v_x_1219_, lean_object* v_x_1220_){
_start:
{
lean_object* v_ks_1221_; lean_object* v_vs_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1246_; 
v_ks_1221_ = lean_ctor_get(v_x_1217_, 0);
v_vs_1222_ = lean_ctor_get(v_x_1217_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_x_1217_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1224_ = v_x_1217_;
v_isShared_1225_ = v_isSharedCheck_1246_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_vs_1222_);
lean_inc(v_ks_1221_);
lean_dec(v_x_1217_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1246_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_array_get_size(v_ks_1221_);
v___x_1227_ = lean_nat_dec_lt(v_x_1218_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
lean_dec(v_x_1218_);
v___x_1228_ = lean_array_push(v_ks_1221_, v_x_1219_);
v___x_1229_ = lean_array_push(v_vs_1222_, v_x_1220_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v___x_1229_);
lean_ctor_set(v___x_1224_, 0, v___x_1228_);
v___x_1231_ = v___x_1224_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
else
{
lean_object* v_k_x27_1233_; uint8_t v___x_1234_; 
v_k_x27_1233_ = lean_array_fget_borrowed(v_ks_1221_, v_x_1218_);
v___x_1234_ = l_Lean_instBEqMVarId_beq(v_x_1219_, v_k_x27_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1236_; 
if (v_isShared_1225_ == 0)
{
v___x_1236_ = v___x_1224_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_ks_1221_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_vs_1222_);
v___x_1236_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_unsigned_to_nat(1u);
v___x_1238_ = lean_nat_add(v_x_1218_, v___x_1237_);
lean_dec(v_x_1218_);
v_x_1217_ = v___x_1236_;
v_x_1218_ = v___x_1238_;
goto _start;
}
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1241_ = lean_array_fset(v_ks_1221_, v_x_1218_, v_x_1219_);
v___x_1242_ = lean_array_fset(v_vs_1222_, v_x_1218_, v_x_1220_);
lean_dec(v_x_1218_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v___x_1242_);
lean_ctor_set(v___x_1224_, 0, v___x_1241_);
v___x_1244_ = v___x_1224_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__19___redArg(lean_object* v_n_1247_, lean_object* v_k_1248_, lean_object* v_v_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__19_spec__21___redArg(v_n_1247_, v___x_1250_, v_k_1248_, v_v_1249_);
return v___x_1251_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg(lean_object* v_x_1253_, size_t v_x_1254_, size_t v_x_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
if (lean_obj_tag(v_x_1253_) == 0)
{
lean_object* v_es_1258_; size_t v___x_1259_; size_t v___x_1260_; lean_object* v_j_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_es_1258_ = lean_ctor_get(v_x_1253_, 0);
v___x_1259_ = ((size_t)31ULL);
v___x_1260_ = lean_usize_land(v_x_1254_, v___x_1259_);
v_j_1261_ = lean_usize_to_nat(v___x_1260_);
v___x_1262_ = lean_array_get_size(v_es_1258_);
v___x_1263_ = lean_nat_dec_lt(v_j_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_dec(v_j_1261_);
lean_dec(v_x_1257_);
lean_dec(v_x_1256_);
return v_x_1253_;
}
else
{
lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1302_; 
lean_inc_ref(v_es_1258_);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_x_1253_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; 
v_unused_1303_ = lean_ctor_get(v_x_1253_, 0);
lean_dec(v_unused_1303_);
v___x_1265_ = v_x_1253_;
v_isShared_1266_ = v_isSharedCheck_1302_;
goto v_resetjp_1264_;
}
else
{
lean_dec(v_x_1253_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1302_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v_v_1267_; lean_object* v___x_1268_; lean_object* v_xs_x27_1269_; lean_object* v___y_1271_; 
v_v_1267_ = lean_array_fget(v_es_1258_, v_j_1261_);
v___x_1268_ = lean_box(0);
v_xs_x27_1269_ = lean_array_fset(v_es_1258_, v_j_1261_, v___x_1268_);
switch(lean_obj_tag(v_v_1267_))
{
case 0:
{
lean_object* v_key_1276_; lean_object* v_val_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1287_; 
v_key_1276_ = lean_ctor_get(v_v_1267_, 0);
v_val_1277_ = lean_ctor_get(v_v_1267_, 1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_v_1267_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1279_ = v_v_1267_;
v_isShared_1280_ = v_isSharedCheck_1287_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_val_1277_);
lean_inc(v_key_1276_);
lean_dec(v_v_1267_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1287_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
uint8_t v___x_1281_; 
v___x_1281_ = l_Lean_instBEqMVarId_beq(v_x_1256_, v_key_1276_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_del_object(v___x_1279_);
v___x_1282_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1276_, v_val_1277_, v_x_1256_, v_x_1257_);
v___x_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
v___y_1271_ = v___x_1283_;
goto v___jp_1270_;
}
else
{
lean_object* v___x_1285_; 
lean_dec(v_val_1277_);
lean_dec(v_key_1276_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v_x_1257_);
lean_ctor_set(v___x_1279_, 0, v_x_1256_);
v___x_1285_ = v___x_1279_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_x_1256_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_x_1257_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
v___y_1271_ = v___x_1285_;
goto v___jp_1270_;
}
}
}
}
case 1:
{
lean_object* v_node_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1300_; 
v_node_1288_ = lean_ctor_get(v_v_1267_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_v_1267_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1290_ = v_v_1267_;
v_isShared_1291_ = v_isSharedCheck_1300_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_node_1288_);
lean_dec(v_v_1267_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1300_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
size_t v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; size_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1292_ = ((size_t)5ULL);
v___x_1293_ = lean_usize_shift_right(v_x_1254_, v___x_1292_);
v___x_1294_ = ((size_t)1ULL);
v___x_1295_ = lean_usize_add(v_x_1255_, v___x_1294_);
v___x_1296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg(v_node_1288_, v___x_1293_, v___x_1295_, v_x_1256_, v_x_1257_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1296_);
v___x_1298_ = v___x_1290_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
v___y_1271_ = v___x_1298_;
goto v___jp_1270_;
}
}
}
default: 
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v_x_1256_);
lean_ctor_set(v___x_1301_, 1, v_x_1257_);
v___y_1271_ = v___x_1301_;
goto v___jp_1270_;
}
}
v___jp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1272_ = lean_array_fset(v_xs_x27_1269_, v_j_1261_, v___y_1271_);
lean_dec(v_j_1261_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1272_);
v___x_1274_ = v___x_1265_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
else
{
lean_object* v_ks_1304_; lean_object* v_vs_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1325_; 
v_ks_1304_ = lean_ctor_get(v_x_1253_, 0);
v_vs_1305_ = lean_ctor_get(v_x_1253_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_x_1253_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1307_ = v_x_1253_;
v_isShared_1308_ = v_isSharedCheck_1325_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_vs_1305_);
lean_inc(v_ks_1304_);
lean_dec(v_x_1253_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1325_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_ks_1304_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_vs_1305_);
v___x_1310_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v_newNode_1311_; uint8_t v___y_1313_; size_t v___x_1319_; uint8_t v___x_1320_; 
v_newNode_1311_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__19___redArg(v___x_1310_, v_x_1256_, v_x_1257_);
v___x_1319_ = ((size_t)7ULL);
v___x_1320_ = lean_usize_dec_le(v___x_1319_, v_x_1255_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1321_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1311_);
v___x_1322_ = lean_unsigned_to_nat(4u);
v___x_1323_ = lean_nat_dec_lt(v___x_1321_, v___x_1322_);
lean_dec(v___x_1321_);
v___y_1313_ = v___x_1323_;
goto v___jp_1312_;
}
else
{
v___y_1313_ = v___x_1320_;
goto v___jp_1312_;
}
v___jp_1312_:
{
if (v___y_1313_ == 0)
{
lean_object* v_ks_1314_; lean_object* v_vs_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_ks_1314_ = lean_ctor_get(v_newNode_1311_, 0);
lean_inc_ref(v_ks_1314_);
v_vs_1315_ = lean_ctor_get(v_newNode_1311_, 1);
lean_inc_ref(v_vs_1315_);
lean_dec_ref(v_newNode_1311_);
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg___closed__0);
v___x_1318_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__20___redArg(v_x_1255_, v_ks_1314_, v_vs_1315_, v___x_1316_, v___x_1317_);
lean_dec_ref(v_vs_1315_);
lean_dec_ref(v_ks_1314_);
return v___x_1318_;
}
else
{
return v_newNode_1311_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__20___redArg(size_t v_depth_1326_, lean_object* v_keys_1327_, lean_object* v_vals_1328_, lean_object* v_i_1329_, lean_object* v_entries_1330_){
_start:
{
lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1331_ = lean_array_get_size(v_keys_1327_);
v___x_1332_ = lean_nat_dec_lt(v_i_1329_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_dec(v_i_1329_);
return v_entries_1330_;
}
else
{
lean_object* v_k_1333_; lean_object* v_v_1334_; uint64_t v___x_1335_; size_t v_h_1336_; size_t v___x_1337_; lean_object* v___x_1338_; size_t v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; size_t v_h_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_k_1333_ = lean_array_fget_borrowed(v_keys_1327_, v_i_1329_);
v_v_1334_ = lean_array_fget_borrowed(v_vals_1328_, v_i_1329_);
v___x_1335_ = l_Lean_instHashableMVarId_hash(v_k_1333_);
v_h_1336_ = lean_uint64_to_usize(v___x_1335_);
v___x_1337_ = ((size_t)5ULL);
v___x_1338_ = lean_unsigned_to_nat(1u);
v___x_1339_ = ((size_t)1ULL);
v___x_1340_ = lean_usize_sub(v_depth_1326_, v___x_1339_);
v___x_1341_ = lean_usize_mul(v___x_1337_, v___x_1340_);
v_h_1342_ = lean_usize_shift_right(v_h_1336_, v___x_1341_);
v___x_1343_ = lean_nat_add(v_i_1329_, v___x_1338_);
lean_dec(v_i_1329_);
lean_inc(v_v_1334_);
lean_inc(v_k_1333_);
v___x_1344_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg(v_entries_1330_, v_h_1342_, v_depth_1326_, v_k_1333_, v_v_1334_);
v_i_1329_ = v___x_1343_;
v_entries_1330_ = v___x_1344_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__20___redArg___boxed(lean_object* v_depth_1346_, lean_object* v_keys_1347_, lean_object* v_vals_1348_, lean_object* v_i_1349_, lean_object* v_entries_1350_){
_start:
{
size_t v_depth_boxed_1351_; lean_object* v_res_1352_; 
v_depth_boxed_1351_ = lean_unbox_usize(v_depth_1346_);
lean_dec(v_depth_1346_);
v_res_1352_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__20___redArg(v_depth_boxed_1351_, v_keys_1347_, v_vals_1348_, v_i_1349_, v_entries_1350_);
lean_dec_ref(v_vals_1348_);
lean_dec_ref(v_keys_1347_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg___boxed(lean_object* v_x_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_, lean_object* v_x_1357_){
_start:
{
size_t v_x_41199__boxed_1358_; size_t v_x_41200__boxed_1359_; lean_object* v_res_1360_; 
v_x_41199__boxed_1358_ = lean_unbox_usize(v_x_1354_);
lean_dec(v_x_1354_);
v_x_41200__boxed_1359_ = lean_unbox_usize(v_x_1355_);
lean_dec(v_x_1355_);
v_res_1360_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg(v_x_1353_, v_x_41199__boxed_1358_, v_x_41200__boxed_1359_, v_x_1356_, v_x_1357_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6___redArg(lean_object* v_x_1361_, lean_object* v_x_1362_, lean_object* v_x_1363_){
_start:
{
uint64_t v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; lean_object* v___x_1367_; 
v___x_1364_ = l_Lean_instHashableMVarId_hash(v_x_1362_);
v___x_1365_ = lean_uint64_to_usize(v___x_1364_);
v___x_1366_ = ((size_t)1ULL);
v___x_1367_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg(v_x_1361_, v___x_1365_, v___x_1366_, v_x_1362_, v_x_1363_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___redArg(lean_object* v_mvarId_1368_, lean_object* v_val_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v_mctx_1373_; lean_object* v_cache_1374_; lean_object* v_zetaDeltaFVarIds_1375_; lean_object* v_postponed_1376_; lean_object* v_diag_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1406_; 
v___x_1372_ = lean_st_ref_take(v___y_1370_);
v_mctx_1373_ = lean_ctor_get(v___x_1372_, 0);
v_cache_1374_ = lean_ctor_get(v___x_1372_, 1);
v_zetaDeltaFVarIds_1375_ = lean_ctor_get(v___x_1372_, 2);
v_postponed_1376_ = lean_ctor_get(v___x_1372_, 3);
v_diag_1377_ = lean_ctor_get(v___x_1372_, 4);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1379_ = v___x_1372_;
v_isShared_1380_ = v_isSharedCheck_1406_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_diag_1377_);
lean_inc(v_postponed_1376_);
lean_inc(v_zetaDeltaFVarIds_1375_);
lean_inc(v_cache_1374_);
lean_inc(v_mctx_1373_);
lean_dec(v___x_1372_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1406_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v_depth_1381_; lean_object* v_levelAssignDepth_1382_; lean_object* v_lmvarCounter_1383_; lean_object* v_mvarCounter_1384_; lean_object* v_lDecls_1385_; lean_object* v_decls_1386_; lean_object* v_userNames_1387_; lean_object* v_lAssignment_1388_; lean_object* v_eAssignment_1389_; lean_object* v_dAssignment_1390_; lean_object* v_instanceTypedMVars_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1405_; 
v_depth_1381_ = lean_ctor_get(v_mctx_1373_, 0);
v_levelAssignDepth_1382_ = lean_ctor_get(v_mctx_1373_, 1);
v_lmvarCounter_1383_ = lean_ctor_get(v_mctx_1373_, 2);
v_mvarCounter_1384_ = lean_ctor_get(v_mctx_1373_, 3);
v_lDecls_1385_ = lean_ctor_get(v_mctx_1373_, 4);
v_decls_1386_ = lean_ctor_get(v_mctx_1373_, 5);
v_userNames_1387_ = lean_ctor_get(v_mctx_1373_, 6);
v_lAssignment_1388_ = lean_ctor_get(v_mctx_1373_, 7);
v_eAssignment_1389_ = lean_ctor_get(v_mctx_1373_, 8);
v_dAssignment_1390_ = lean_ctor_get(v_mctx_1373_, 9);
v_instanceTypedMVars_1391_ = lean_ctor_get(v_mctx_1373_, 10);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_mctx_1373_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1393_ = v_mctx_1373_;
v_isShared_1394_ = v_isSharedCheck_1405_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_instanceTypedMVars_1391_);
lean_inc(v_dAssignment_1390_);
lean_inc(v_eAssignment_1389_);
lean_inc(v_lAssignment_1388_);
lean_inc(v_userNames_1387_);
lean_inc(v_decls_1386_);
lean_inc(v_lDecls_1385_);
lean_inc(v_mvarCounter_1384_);
lean_inc(v_lmvarCounter_1383_);
lean_inc(v_levelAssignDepth_1382_);
lean_inc(v_depth_1381_);
lean_dec(v_mctx_1373_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1405_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1395_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6___redArg(v_eAssignment_1389_, v_mvarId_1368_, v_val_1369_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 8, v___x_1395_);
v___x_1397_ = v___x_1393_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_depth_1381_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_levelAssignDepth_1382_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v_lmvarCounter_1383_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v_mvarCounter_1384_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v_lDecls_1385_);
lean_ctor_set(v_reuseFailAlloc_1404_, 5, v_decls_1386_);
lean_ctor_set(v_reuseFailAlloc_1404_, 6, v_userNames_1387_);
lean_ctor_set(v_reuseFailAlloc_1404_, 7, v_lAssignment_1388_);
lean_ctor_set(v_reuseFailAlloc_1404_, 8, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1404_, 9, v_dAssignment_1390_);
lean_ctor_set(v_reuseFailAlloc_1404_, 10, v_instanceTypedMVars_1391_);
v___x_1397_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1399_; 
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1397_);
v___x_1399_ = v___x_1379_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_cache_1374_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_zetaDeltaFVarIds_1375_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v_postponed_1376_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v_diag_1377_);
v___x_1399_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = lean_st_ref_put(v___y_1370_, v___x_1399_);
v___x_1401_ = lean_box(0);
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___redArg___boxed(lean_object* v_mvarId_1407_, lean_object* v_val_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___redArg(v_mvarId_1407_, v_val_1408_, v___y_1409_);
lean_dec(v___y_1409_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2_spec__5___redArg(lean_object* v_m_1412_, lean_object* v_query_1413_, lean_object* v_x_1414_, lean_object* v_x_1415_, lean_object* v_x_1416_){
_start:
{
lean_object* v_zero_1417_; uint8_t v_isZero_1418_; 
v_zero_1417_ = lean_unsigned_to_nat(0u);
v_isZero_1418_ = lean_nat_dec_eq(v_x_1415_, v_zero_1417_);
if (v_isZero_1418_ == 1)
{
lean_dec(v_x_1416_);
lean_dec(v_x_1415_);
if (lean_obj_tag(v_x_1414_) == 0)
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_box(2);
return v___x_1419_;
}
else
{
lean_object* v_val_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
v_val_1420_ = lean_ctor_get(v_x_1414_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_x_1414_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v_x_1414_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_val_1420_);
lean_dec(v_x_1414_);
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
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_val_1420_);
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
else
{
lean_object* v_keyArray_1428_; lean_object* v_valueArray_1429_; lean_object* v___x_1430_; uint8_t v_isSome_1431_; 
v_keyArray_1428_ = lean_ctor_get(v_m_1412_, 1);
v_valueArray_1429_ = lean_ctor_get(v_m_1412_, 2);
v___x_1430_ = lean_array_fget_borrowed(v_keyArray_1428_, v_x_1416_);
v_isSome_1431_ = lean_noption_is_some(v___x_1430_);
if (v_isSome_1431_ == 0)
{
lean_dec(v_x_1415_);
if (lean_obj_tag(v_x_1414_) == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_x_1416_);
return v___x_1432_;
}
else
{
lean_object* v_val_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec(v_x_1416_);
v_val_1433_ = lean_ctor_get(v_x_1414_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_x_1414_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v_x_1414_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_val_1433_);
lean_dec(v_x_1414_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_val_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v_one_1441_; lean_object* v_n_1442_; lean_object* v___y_1444_; 
v_one_1441_ = lean_unsigned_to_nat(1u);
v_n_1442_ = lean_nat_sub(v_x_1415_, v_one_1441_);
lean_dec(v_x_1415_);
if (v_isSome_1431_ == 0)
{
goto v___jp_1450_;
}
else
{
lean_object* v___x_1452_; uint8_t v_isSome_1453_; 
v___x_1452_ = lean_array_fget_borrowed(v_valueArray_1429_, v_x_1416_);
v_isSome_1453_ = lean_noption_is_some(v___x_1452_);
if (v_isSome_1453_ == 0)
{
goto v___jp_1450_;
}
else
{
lean_object* v_val_1454_; uint8_t v___x_1455_; 
lean_inc(v___x_1430_);
v_val_1454_ = lean_noption_get(v___x_1430_);
v___x_1455_ = lean_nat_dec_eq(v_val_1454_, v_query_1413_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
lean_dec(v_val_1454_);
v___x_1456_ = lean_array_get_size(v_keyArray_1428_);
v___x_1457_ = lean_nat_add(v_x_1416_, v_one_1441_);
lean_dec(v_x_1416_);
v___x_1458_ = lean_nat_dec_lt(v___x_1457_, v___x_1456_);
if (v___x_1458_ == 0)
{
lean_dec(v___x_1457_);
v_x_1415_ = v_n_1442_;
v_x_1416_ = v_zero_1417_;
goto _start;
}
else
{
v_x_1415_ = v_n_1442_;
v_x_1416_ = v___x_1457_;
goto _start;
}
}
else
{
lean_object* v_val_1461_; lean_object* v___x_1462_; 
lean_dec(v_n_1442_);
lean_dec(v_x_1414_);
lean_inc(v___x_1452_);
v_val_1461_ = lean_noption_get(v___x_1452_);
v___x_1462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1462_, 0, v_x_1416_);
lean_ctor_set(v___x_1462_, 1, v_val_1454_);
lean_ctor_set(v___x_1462_, 2, v_val_1461_);
return v___x_1462_;
}
}
}
v___jp_1443_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1445_ = lean_array_get_size(v_keyArray_1428_);
v___x_1446_ = lean_nat_add(v_x_1416_, v_one_1441_);
lean_dec(v_x_1416_);
v___x_1447_ = lean_nat_dec_lt(v___x_1446_, v___x_1445_);
if (v___x_1447_ == 0)
{
lean_dec(v___x_1446_);
v_x_1414_ = v___y_1444_;
v_x_1415_ = v_n_1442_;
v_x_1416_ = v_zero_1417_;
goto _start;
}
else
{
v_x_1414_ = v___y_1444_;
v_x_1415_ = v_n_1442_;
v_x_1416_ = v___x_1446_;
goto _start;
}
}
v___jp_1450_:
{
if (lean_obj_tag(v_x_1414_) == 0)
{
lean_object* v___x_1451_; 
lean_inc(v_x_1416_);
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_x_1416_);
v___y_1444_ = v___x_1451_;
goto v___jp_1443_;
}
else
{
v___y_1444_ = v_x_1414_;
goto v___jp_1443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_m_1463_, lean_object* v_query_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2_spec__5___redArg(v_m_1463_, v_query_1464_, v_x_1465_, v_x_1466_, v_x_1467_);
lean_dec(v_query_1464_);
lean_dec_ref(v_m_1463_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2___redArg(lean_object* v_m_1469_, lean_object* v_query_1470_){
_start:
{
lean_object* v_keyArray_1471_; lean_object* v___x_1472_; uint64_t v___x_1473_; uint64_t v___x_1474_; uint64_t v___x_1475_; uint64_t v_fold_1476_; uint64_t v___x_1477_; uint64_t v___x_1478_; uint64_t v___x_1479_; size_t v___x_1480_; size_t v___x_1481_; size_t v___x_1482_; size_t v___x_1483_; size_t v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_keyArray_1471_ = lean_ctor_get(v_m_1469_, 1);
v___x_1472_ = lean_array_get_size(v_keyArray_1471_);
v___x_1473_ = lean_uint64_of_nat(v_query_1470_);
v___x_1474_ = 32ULL;
v___x_1475_ = lean_uint64_shift_right(v___x_1473_, v___x_1474_);
v_fold_1476_ = lean_uint64_xor(v___x_1473_, v___x_1475_);
v___x_1477_ = 16ULL;
v___x_1478_ = lean_uint64_shift_right(v_fold_1476_, v___x_1477_);
v___x_1479_ = lean_uint64_xor(v_fold_1476_, v___x_1478_);
v___x_1480_ = lean_uint64_to_usize(v___x_1479_);
v___x_1481_ = lean_usize_of_nat(v___x_1472_);
v___x_1482_ = ((size_t)1ULL);
v___x_1483_ = lean_usize_sub(v___x_1481_, v___x_1482_);
v___x_1484_ = lean_usize_land(v___x_1480_, v___x_1483_);
v___x_1485_ = lean_usize_to_nat(v___x_1484_);
v___x_1486_ = lean_box(0);
v___x_1487_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2_spec__5___redArg(v_m_1469_, v_query_1470_, v___x_1486_, v___x_1472_, v___x_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2___redArg___boxed(lean_object* v_m_1488_, lean_object* v_query_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2___redArg(v_m_1488_, v_query_1489_);
lean_dec(v_query_1489_);
lean_dec_ref(v_m_1488_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7_spec__15___redArg(lean_object* v_b_1491_, lean_object* v_acc_1492_, lean_object* v_i_1493_){
_start:
{
lean_object* v___y_1495_; lean_object* v_keyArray_1503_; lean_object* v_valueArray_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v_keyArray_1503_ = lean_ctor_get(v_b_1491_, 1);
v_valueArray_1504_ = lean_ctor_get(v_b_1491_, 2);
v___x_1505_ = lean_array_get_size(v_keyArray_1503_);
v___x_1506_ = lean_nat_dec_lt(v_i_1493_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_dec(v_i_1493_);
return v_acc_1492_;
}
else
{
lean_object* v___x_1507_; uint8_t v_isSome_1508_; 
v___x_1507_ = lean_array_fget_borrowed(v_keyArray_1503_, v_i_1493_);
v_isSome_1508_ = lean_noption_is_some(v___x_1507_);
if (v_isSome_1508_ == 0)
{
goto v___jp_1499_;
}
else
{
lean_object* v___x_1509_; uint8_t v_isSome_1510_; 
v___x_1509_ = lean_array_fget_borrowed(v_valueArray_1504_, v_i_1493_);
v_isSome_1510_ = lean_noption_is_some(v___x_1509_);
if (v_isSome_1510_ == 0)
{
goto v___jp_1499_;
}
else
{
lean_object* v_val_1511_; lean_object* v_val_1512_; lean_object* v_i_1514_; lean_object* v___x_1519_; 
lean_inc(v___x_1507_);
v_val_1511_ = lean_noption_get(v___x_1507_);
lean_inc(v___x_1509_);
v_val_1512_ = lean_noption_get(v___x_1509_);
v___x_1519_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2___redArg(v_acc_1492_, v_val_1511_);
switch(lean_obj_tag(v___x_1519_))
{
case 0:
{
lean_object* v_index_1520_; lean_object* v_size_1521_; lean_object* v___x_1522_; 
v_index_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_index_1520_);
lean_dec_ref_known(v___x_1519_, 3);
v_size_1521_ = lean_ctor_get(v_acc_1492_, 0);
lean_inc(v_size_1521_);
v___x_1522_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1492_, v_size_1521_, v_index_1520_, v_val_1511_, v_val_1512_);
lean_dec(v_index_1520_);
v___y_1495_ = v___x_1522_;
goto v___jp_1494_;
}
case 1:
{
lean_object* v_index_1523_; 
v_index_1523_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_index_1523_);
lean_dec_ref_known(v___x_1519_, 1);
v_i_1514_ = v_index_1523_;
goto v___jp_1513_;
}
default: 
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1492_, v___x_1524_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_index_1526_; 
v_index_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_index_1526_);
lean_dec_ref_known(v___x_1525_, 1);
v_i_1514_ = v_index_1526_;
goto v___jp_1513_;
}
else
{
lean_dec(v_val_1512_);
lean_dec(v_val_1511_);
v___y_1495_ = v_acc_1492_;
goto v___jp_1494_;
}
}
}
v___jp_1513_:
{
lean_object* v_size_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v_size_1515_ = lean_ctor_get(v_acc_1492_, 0);
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_nat_add(v_size_1515_, v___x_1516_);
v___x_1518_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1492_, v___x_1517_, v_i_1514_, v_val_1511_, v_val_1512_);
lean_dec(v_i_1514_);
v___y_1495_ = v___x_1518_;
goto v___jp_1494_;
}
}
}
}
v___jp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_unsigned_to_nat(1u);
v___x_1497_ = lean_nat_add(v_i_1493_, v___x_1496_);
lean_dec(v_i_1493_);
v_acc_1492_ = v___y_1495_;
v_i_1493_ = v___x_1497_;
goto _start;
}
v___jp_1499_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_unsigned_to_nat(1u);
v___x_1501_ = lean_nat_add(v_i_1493_, v___x_1500_);
lean_dec(v_i_1493_);
v_i_1493_ = v___x_1501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7_spec__15___redArg___boxed(lean_object* v_b_1527_, lean_object* v_acc_1528_, lean_object* v_i_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7_spec__15___redArg(v_b_1527_, v_acc_1528_, v_i_1529_);
lean_dec_ref(v_b_1527_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7___redArg(lean_object* v_init_1531_, lean_object* v_b_1532_){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_unsigned_to_nat(0u);
v___x_1534_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7_spec__15___redArg(v_b_1532_, v_init_1531_, v___x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7___redArg___boxed(lean_object* v_init_1535_, lean_object* v_b_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7___redArg(v_init_1535_, v_b_1536_);
lean_dec_ref(v_b_1536_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3___redArg(lean_object* v_m_1538_){
_start:
{
lean_object* v_keyArray_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v_cellCount_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v_target_1546_; lean_object* v___x_1547_; 
v_keyArray_1539_ = lean_ctor_get(v_m_1538_, 1);
v___x_1540_ = lean_array_get_size(v_keyArray_1539_);
v___x_1541_ = lean_unsigned_to_nat(2u);
v_cellCount_1542_ = lean_nat_mul(v___x_1540_, v___x_1541_);
v___x_1543_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1542_);
v___x_1544_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1542_);
v___x_1545_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1542_);
v_target_1546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1546_, 0, v___x_1543_);
lean_ctor_set(v_target_1546_, 1, v___x_1544_);
lean_ctor_set(v_target_1546_, 2, v___x_1545_);
v___x_1547_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7___redArg(v_target_1546_, v_m_1538_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3___redArg___boxed(lean_object* v_m_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3___redArg(v_m_1548_);
lean_dec_ref(v_m_1548_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(lean_object* v_as_x27_1550_, lean_object* v_b_1551_){
_start:
{
if (lean_obj_tag(v_as_x27_1550_) == 0)
{
return v_b_1551_;
}
else
{
lean_object* v_head_1552_; lean_object* v_tail_1553_; lean_object* v_fst_1554_; lean_object* v_snd_1555_; lean_object* v___y_1557_; lean_object* v_i_1558_; lean_object* v___y_1565_; lean_object* v___y_1577_; lean_object* v_i_1578_; lean_object* v___x_1596_; 
v_head_1552_ = lean_ctor_get(v_as_x27_1550_, 0);
v_tail_1553_ = lean_ctor_get(v_as_x27_1550_, 1);
v_fst_1554_ = lean_ctor_get(v_head_1552_, 0);
v_snd_1555_ = lean_ctor_get(v_head_1552_, 1);
v___x_1596_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2___redArg(v_b_1551_, v_fst_1554_);
switch(lean_obj_tag(v___x_1596_))
{
case 0:
{
lean_object* v_index_1597_; lean_object* v_size_1598_; lean_object* v___x_1599_; 
v_index_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_index_1597_);
lean_dec_ref_known(v___x_1596_, 3);
v_size_1598_ = lean_ctor_get(v_b_1551_, 0);
lean_inc(v_size_1598_);
lean_inc(v_snd_1555_);
lean_inc(v_fst_1554_);
v___x_1599_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_1551_, v_size_1598_, v_index_1597_, v_fst_1554_, v_snd_1555_);
lean_dec(v_index_1597_);
v_as_x27_1550_ = v_tail_1553_;
v_b_1551_ = v___x_1599_;
goto _start;
}
case 1:
{
lean_object* v_index_1601_; lean_object* v_size_1602_; lean_object* v_keyArray_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v_index_1601_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_index_1601_);
lean_dec_ref_known(v___x_1596_, 1);
v_size_1602_ = lean_ctor_get(v_b_1551_, 0);
v_keyArray_1603_ = lean_ctor_get(v_b_1551_, 1);
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = lean_nat_add(v_size_1602_, v___x_1604_);
v___x_1606_ = lean_array_get_size(v_keyArray_1603_);
v___x_1607_ = lean_nat_dec_lt(v___x_1605_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_dec(v___x_1605_);
lean_dec(v_index_1601_);
goto v___jp_1584_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1608_ = lean_unsigned_to_nat(4u);
v___x_1609_ = lean_nat_mul(v___x_1605_, v___x_1608_);
v___x_1610_ = lean_unsigned_to_nat(3u);
v___x_1611_ = lean_nat_mul(v___x_1606_, v___x_1610_);
v___x_1612_ = lean_nat_dec_le(v___x_1609_, v___x_1611_);
lean_dec(v___x_1611_);
lean_dec(v___x_1609_);
if (v___x_1612_ == 0)
{
lean_dec(v___x_1605_);
lean_dec(v_index_1601_);
goto v___jp_1584_;
}
else
{
lean_object* v___x_1613_; 
lean_inc(v_snd_1555_);
lean_inc(v_fst_1554_);
v___x_1613_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_1551_, v___x_1605_, v_index_1601_, v_fst_1554_, v_snd_1555_);
lean_dec(v_index_1601_);
v_as_x27_1550_ = v_tail_1553_;
v_b_1551_ = v___x_1613_;
goto _start;
}
}
}
default: 
{
lean_object* v_size_1615_; lean_object* v_keyArray_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_size_1615_ = lean_ctor_get(v_b_1551_, 0);
v_keyArray_1616_ = lean_ctor_get(v_b_1551_, 1);
v___x_1617_ = lean_unsigned_to_nat(1u);
v___x_1618_ = lean_nat_add(v_size_1615_, v___x_1617_);
v___x_1619_ = lean_array_get_size(v_keyArray_1616_);
v___x_1620_ = lean_nat_dec_lt(v___x_1618_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; 
lean_dec(v___x_1618_);
v___x_1621_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3___redArg(v_b_1551_);
lean_dec_ref(v_b_1551_);
v___y_1565_ = v___x_1621_;
goto v___jp_1564_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1622_ = lean_unsigned_to_nat(4u);
v___x_1623_ = lean_nat_mul(v___x_1618_, v___x_1622_);
lean_dec(v___x_1618_);
v___x_1624_ = lean_unsigned_to_nat(3u);
v___x_1625_ = lean_nat_mul(v___x_1619_, v___x_1624_);
v___x_1626_ = lean_nat_dec_le(v___x_1623_, v___x_1625_);
lean_dec(v___x_1625_);
lean_dec(v___x_1623_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3___redArg(v_b_1551_);
lean_dec_ref(v_b_1551_);
v___y_1565_ = v___x_1627_;
goto v___jp_1564_;
}
else
{
v___y_1565_ = v_b_1551_;
goto v___jp_1564_;
}
}
}
}
v___jp_1556_:
{
lean_object* v_size_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_size_1559_ = lean_ctor_get(v___y_1557_, 0);
v___x_1560_ = lean_unsigned_to_nat(1u);
v___x_1561_ = lean_nat_add(v_size_1559_, v___x_1560_);
lean_inc(v_snd_1555_);
lean_inc(v_fst_1554_);
v___x_1562_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1557_, v___x_1561_, v_i_1558_, v_fst_1554_, v_snd_1555_);
lean_dec(v_i_1558_);
v_as_x27_1550_ = v_tail_1553_;
v_b_1551_ = v___x_1562_;
goto _start;
}
v___jp_1564_:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2___redArg(v___y_1565_, v_fst_1554_);
switch(lean_obj_tag(v___x_1566_))
{
case 0:
{
lean_object* v_index_1567_; lean_object* v_size_1568_; lean_object* v___x_1569_; 
v_index_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_index_1567_);
lean_dec_ref_known(v___x_1566_, 3);
v_size_1568_ = lean_ctor_get(v___y_1565_, 0);
lean_inc(v_size_1568_);
lean_inc(v_snd_1555_);
lean_inc(v_fst_1554_);
v___x_1569_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1565_, v_size_1568_, v_index_1567_, v_fst_1554_, v_snd_1555_);
lean_dec(v_index_1567_);
v_as_x27_1550_ = v_tail_1553_;
v_b_1551_ = v___x_1569_;
goto _start;
}
case 1:
{
lean_object* v_index_1571_; 
v_index_1571_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_index_1571_);
lean_dec_ref_known(v___x_1566_, 1);
v___y_1557_ = v___y_1565_;
v_i_1558_ = v_index_1571_;
goto v___jp_1556_;
}
default: 
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1565_, v___x_1572_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_index_1574_; 
v_index_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_index_1574_);
lean_dec_ref_known(v___x_1573_, 1);
v___y_1557_ = v___y_1565_;
v_i_1558_ = v_index_1574_;
goto v___jp_1556_;
}
else
{
v_as_x27_1550_ = v_tail_1553_;
v_b_1551_ = v___y_1565_;
goto _start;
}
}
}
}
v___jp_1576_:
{
lean_object* v_size_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v_size_1579_ = lean_ctor_get(v___y_1577_, 0);
v___x_1580_ = lean_unsigned_to_nat(1u);
v___x_1581_ = lean_nat_add(v_size_1579_, v___x_1580_);
lean_inc(v_snd_1555_);
lean_inc(v_fst_1554_);
v___x_1582_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1577_, v___x_1581_, v_i_1578_, v_fst_1554_, v_snd_1555_);
lean_dec(v_i_1578_);
v_as_x27_1550_ = v_tail_1553_;
v_b_1551_ = v___x_1582_;
goto _start;
}
v___jp_1584_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3___redArg(v_b_1551_);
lean_dec_ref(v_b_1551_);
v___x_1586_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2___redArg(v___x_1585_, v_fst_1554_);
switch(lean_obj_tag(v___x_1586_))
{
case 0:
{
lean_object* v_index_1587_; lean_object* v_size_1588_; lean_object* v___x_1589_; 
v_index_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_index_1587_);
lean_dec_ref_known(v___x_1586_, 3);
v_size_1588_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_size_1588_);
lean_inc(v_snd_1555_);
lean_inc(v_fst_1554_);
v___x_1589_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1585_, v_size_1588_, v_index_1587_, v_fst_1554_, v_snd_1555_);
lean_dec(v_index_1587_);
v_as_x27_1550_ = v_tail_1553_;
v_b_1551_ = v___x_1589_;
goto _start;
}
case 1:
{
lean_object* v_index_1591_; 
v_index_1591_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_index_1591_);
lean_dec_ref_known(v___x_1586_, 1);
v___y_1577_ = v___x_1585_;
v_i_1578_ = v_index_1591_;
goto v___jp_1576_;
}
default: 
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_unsigned_to_nat(0u);
v___x_1593_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1585_, v___x_1592_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_index_1594_; 
v_index_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_index_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v___y_1577_ = v___x_1585_;
v_i_1578_ = v_index_1594_;
goto v___jp_1576_;
}
else
{
v_as_x27_1550_ = v_tail_1553_;
v_b_1551_ = v___x_1585_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg___boxed(lean_object* v_as_x27_1628_, lean_object* v_b_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(v_as_x27_1628_, v_b_1629_);
lean_dec(v_as_x27_1628_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(lean_object* v_m_1631_, lean_object* v_l_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(v_l_1632_, v_m_1631_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2___boxed(lean_object* v_m_1634_, lean_object* v_l_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2(v_m_1634_, v_l_1635_);
lean_dec(v_l_1635_);
return v_res_1636_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v_cellCount_1637_; lean_object* v___x_1638_; 
v_cellCount_1637_ = lean_unsigned_to_nat(16u);
v___x_1638_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1637_);
return v___x_1638_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v_cellCount_1639_; lean_object* v___x_1640_; 
v_cellCount_1639_ = lean_unsigned_to_nat(16u);
v___x_1640_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1639_);
return v___x_1640_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1641_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__1);
v___x_1642_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__0);
v___x_1643_ = lean_unsigned_to_nat(0u);
v___x_1644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v___x_1642_);
lean_ctor_set(v___x_1644_, 2, v___x_1641_);
return v___x_1644_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__5));
v___x_1650_ = l_Lean_stringToMessageData(v___x_1649_);
return v___x_1650_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1651_; double v___x_1652_; 
v___x_1651_ = lean_unsigned_to_nat(1000000000u);
v___x_1652_ = lean_float_of_nat(v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(lean_object* v_unsatProver_1653_, lean_object* v_g_1654_, lean_object* v_cls_1655_, uint8_t v___x_1656_, lean_object* v___x_1657_, lean_object* v___f_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v_options_1741_; lean_object* v_inheritedTraceOptions_1742_; uint8_t v_hasTrace_1743_; lean_object* v___y_1745_; 
v_options_1741_ = lean_ctor_get(v___y_1665_, 2);
v_inheritedTraceOptions_1742_ = lean_ctor_get(v___y_1665_, 13);
v_hasTrace_1743_ = lean_ctor_get_uint8(v_options_1741_, sizeof(void*)*1);
if (v_hasTrace_1743_ == 0)
{
lean_object* v___x_1774_; 
lean_dec_ref(v___f_1658_);
lean_dec_ref(v___x_1657_);
lean_inc(v_g_1654_);
v___x_1774_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1654_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
v___y_1745_ = v___x_1774_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v_a_1781_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v_a_1796_; 
v___x_1775_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4));
lean_inc(v_cls_1655_);
v___x_1776_ = l_Lean_Name_append(v___x_1775_, v_cls_1655_);
v___x_1777_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1742_, v_options_1741_, v___x_1776_);
lean_dec(v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1846_ = l_Lean_trace_profiler;
v___x_1847_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(v_options_1741_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; 
lean_dec_ref(v___f_1658_);
lean_dec_ref(v___x_1657_);
lean_inc(v_g_1654_);
v___x_1848_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1654_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
v___y_1745_ = v___x_1848_;
goto v___jp_1744_;
}
else
{
goto v___jp_1805_;
}
}
else
{
goto v___jp_1805_;
}
v___jp_1778_:
{
lean_object* v___x_1782_; double v___x_1783_; double v___x_1784_; double v___x_1785_; double v___x_1786_; double v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1782_ = lean_io_mono_nanos_now();
v___x_1783_ = lean_float_of_nat(v___y_1779_);
v___x_1784_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__7, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__7);
v___x_1785_ = lean_float_div(v___x_1783_, v___x_1784_);
v___x_1786_ = lean_float_of_nat(v___x_1782_);
v___x_1787_ = lean_float_div(v___x_1786_, v___x_1784_);
v___x_1788_ = lean_box_float(v___x_1785_);
v___x_1789_ = lean_box_float(v___x_1787_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v_a_1781_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
lean_inc(v_cls_1655_);
v___x_1792_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_cls_1655_, v___x_1656_, v___x_1657_, v_options_1741_, v___x_1777_, v___y_1780_, v___f_1658_, v___x_1791_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
v___y_1745_ = v___x_1792_;
goto v___jp_1744_;
}
v___jp_1793_:
{
lean_object* v___x_1797_; double v___x_1798_; double v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1797_ = lean_io_get_num_heartbeats();
v___x_1798_ = lean_float_of_nat(v___y_1794_);
v___x_1799_ = lean_float_of_nat(v___x_1797_);
v___x_1800_ = lean_box_float(v___x_1798_);
v___x_1801_ = lean_box_float(v___x_1799_);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v_a_1796_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
lean_inc(v_cls_1655_);
v___x_1804_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8(v_cls_1655_, v___x_1656_, v___x_1657_, v_options_1741_, v___x_1777_, v___y_1795_, v___f_1658_, v___x_1803_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
v___y_1745_ = v___x_1804_;
goto v___jp_1744_;
}
v___jp_1805_:
{
lean_object* v___x_1806_; lean_object* v_a_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1806_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__6___redArg(v___y_1666_);
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
lean_dec_ref(v___x_1806_);
v___x_1808_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1809_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__7(v_options_1741_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_io_mono_nanos_now();
lean_inc(v_g_1654_);
v___x_1811_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1654_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 1);
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
v___y_1779_ = v___x_1810_;
v___y_1780_ = v_a_1807_;
v_a_1781_ = v___x_1817_;
goto v___jp_1778_;
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_a_1820_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1811_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1811_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 0);
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
v___y_1779_ = v___x_1810_;
v___y_1780_ = v_a_1807_;
v_a_1781_ = v___x_1825_;
goto v___jp_1778_;
}
}
}
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = lean_io_get_num_heartbeats();
lean_inc(v_g_1654_);
v___x_1829_ = l_Lean_Meta_Tactic_BVDecide_reflectBV(v_g_1654_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set_tag(v___x_1832_, 1);
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
v___y_1794_ = v___x_1828_;
v___y_1795_ = v_a_1807_;
v_a_1796_ = v___x_1835_;
goto v___jp_1793_;
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
v_a_1838_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1829_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1829_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set_tag(v___x_1840_, 0);
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
v___y_1794_ = v___x_1828_;
v___y_1795_ = v_a_1807_;
v_a_1796_ = v___x_1843_;
goto v___jp_1793_;
}
}
}
}
}
}
v___jp_1668_:
{
lean_object* v___x_1678_; lean_object* v_atoms_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1678_ = lean_st_ref_get(v___y_1671_);
v_atoms_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc_ref(v_atoms_1679_);
lean_dec(v___x_1678_);
v___x_1680_ = lean_box(0);
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__0(v_atoms_1679_, v___x_1680_, v___x_1681_);
lean_dec_ref(v_atoms_1679_);
v___x_1683_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__1(v___x_1682_, v___x_1680_);
v___x_1684_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__2);
v___x_1685_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(v___x_1683_, v___x_1684_);
lean_dec(v___x_1683_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc_ref(v___y_1669_);
lean_inc(v_g_1654_);
v___x_1686_ = lean_apply_8(v_unsatProver_1653_, v_g_1654_, v___y_1669_, v___x_1685_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, lean_box(0));
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1732_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1689_ = v___x_1686_;
v_isShared_1690_ = v_isSharedCheck_1732_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1686_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1732_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
if (lean_obj_tag(v_a_1687_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref(v___y_1669_);
lean_dec(v_g_1654_);
v_a_1691_ = lean_ctor_get(v_a_1687_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_a_1687_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1693_ = v_a_1687_;
v_isShared_1694_ = v_isSharedCheck_1701_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v_a_1687_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1701_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1698_; 
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1696_);
v___x_1698_ = v___x_1689_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1731_; 
lean_del_object(v___x_1689_);
v_a_1702_ = lean_ctor_get(v_a_1687_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_a_1687_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1704_ = v_a_1687_;
v_isShared_1705_ = v_isSharedCheck_1731_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v_a_1687_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1731_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v_proof_1706_; lean_object* v_cert_1707_; lean_object* v_proveFalse_1708_; lean_object* v___x_1709_; 
v_proof_1706_ = lean_ctor_get(v_a_1702_, 0);
lean_inc_ref(v_proof_1706_);
v_cert_1707_ = lean_ctor_get(v_a_1702_, 1);
lean_inc(v_cert_1707_);
lean_dec(v_a_1702_);
v_proveFalse_1708_ = lean_ctor_get(v___y_1669_, 1);
lean_inc_ref(v_proveFalse_1708_);
lean_dec_ref(v___y_1669_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
lean_inc(v___y_1671_);
lean_inc_ref(v___y_1670_);
v___x_1709_ = lean_apply_10(v_proveFalse_1708_, v_proof_1706_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, lean_box(0));
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1721_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v___x_1711_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___redArg(v_g_1654_, v_a_1710_, v___y_1675_);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1721_ == 0)
{
lean_object* v_unused_1722_; 
v_unused_1722_ = lean_ctor_get(v___x_1711_, 0);
lean_dec(v_unused_1722_);
v___x_1713_ = v___x_1711_;
v_isShared_1714_ = v_isSharedCheck_1721_;
goto v_resetjp_1712_;
}
else
{
lean_dec(v___x_1711_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1721_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v_cert_1707_);
v___x_1716_ = v___x_1704_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_cert_1707_);
v___x_1716_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1718_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1716_);
v___x_1718_ = v___x_1713_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
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
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v_cert_1707_);
lean_del_object(v___x_1704_);
lean_dec(v_g_1654_);
v_a_1723_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1709_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1709_);
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
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec_ref(v___y_1669_);
lean_dec(v_g_1654_);
v_a_1733_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1686_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1686_);
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
v___jp_1744_:
{
if (lean_obj_tag(v___y_1745_) == 0)
{
if (v_hasTrace_1743_ == 0)
{
lean_object* v_a_1746_; 
lean_dec(v_cls_1655_);
v_a_1746_ = lean_ctor_get(v___y_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___y_1745_, 1);
v___y_1669_ = v_a_1746_;
v___y_1670_ = v___y_1659_;
v___y_1671_ = v___y_1660_;
v___y_1672_ = v___y_1661_;
v___y_1673_ = v___y_1662_;
v___y_1674_ = v___y_1663_;
v___y_1675_ = v___y_1664_;
v___y_1676_ = v___y_1665_;
v___y_1677_ = v___y_1666_;
goto v___jp_1668_;
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_a_1747_ = lean_ctor_get(v___y_1745_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___y_1745_, 1);
v___x_1748_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__4));
lean_inc(v_cls_1655_);
v___x_1749_ = l_Lean_Name_append(v___x_1748_, v_cls_1655_);
v___x_1750_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1742_, v_options_1741_, v___x_1749_);
lean_dec(v___x_1749_);
if (v___x_1750_ == 0)
{
lean_dec(v_cls_1655_);
v___y_1669_ = v_a_1747_;
v___y_1670_ = v___y_1659_;
v___y_1671_ = v___y_1660_;
v___y_1672_ = v___y_1661_;
v___y_1673_ = v___y_1662_;
v___y_1674_ = v___y_1663_;
v___y_1675_ = v___y_1664_;
v___y_1676_ = v___y_1665_;
v___y_1677_ = v___y_1666_;
goto v___jp_1668_;
}
else
{
lean_object* v_bvExpr_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v_bvExpr_1751_ = lean_ctor_get(v_a_1747_, 0);
v___x_1752_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6, &l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___closed__6);
lean_inc_ref(v_bvExpr_1751_);
v___x_1753_ = l_Std_Tactic_BVDecide_BoolExpr_toString___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__4(v_bvExpr_1751_);
v___x_1754_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
v___x_1755_ = l_Lean_MessageData_ofFormat(v___x_1754_);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1752_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(v_cls_1655_, v___x_1756_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_dec_ref_known(v___x_1757_, 1);
v___y_1669_ = v_a_1747_;
v___y_1670_ = v___y_1659_;
v___y_1671_ = v___y_1660_;
v___y_1672_ = v___y_1661_;
v___y_1673_ = v___y_1662_;
v___y_1674_ = v___y_1663_;
v___y_1675_ = v___y_1664_;
v___y_1676_ = v___y_1665_;
v___y_1677_ = v___y_1666_;
goto v___jp_1668_;
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec(v_a_1747_);
lean_dec(v_g_1654_);
lean_dec_ref(v_unsatProver_1653_);
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
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
}
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_dec(v_cls_1655_);
lean_dec(v_g_1654_);
lean_dec_ref(v_unsatProver_1653_);
v_a_1766_ = lean_ctor_get(v___y_1745_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___y_1745_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___y_1745_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___y_1745_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed(lean_object* v_unsatProver_1849_, lean_object* v_g_1850_, lean_object* v_cls_1851_, lean_object* v___x_1852_, lean_object* v___x_1853_, lean_object* v___f_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
uint8_t v___x_41763__boxed_1864_; lean_object* v_res_1865_; 
v___x_41763__boxed_1864_ = lean_unbox(v___x_1852_);
v_res_1865_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1(v_unsatProver_1849_, v_g_1850_, v_cls_1851_, v___x_41763__boxed_1864_, v___x_1853_, v___f_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(lean_object* v_g_1874_, lean_object* v_unsatProver_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v___f_1885_; lean_object* v_cls_1886_; uint8_t v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___f_1890_; lean_object* v___x_1891_; 
v___f_1885_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__0));
v_cls_1886_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___closed__4));
v___x_1887_ = 1;
v___x_1888_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg___closed__1));
v___x_1889_ = lean_box(v___x_1887_);
lean_inc(v_g_1874_);
v___f_1890_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___lam__1___boxed), 15, 6);
lean_closure_set(v___f_1890_, 0, v_unsatProver_1875_);
lean_closure_set(v___f_1890_, 1, v_g_1874_);
lean_closure_set(v___f_1890_, 2, v_cls_1886_);
lean_closure_set(v___f_1890_, 3, v___x_1889_);
lean_closure_set(v___f_1890_, 4, v___x_1888_);
lean_closure_set(v___f_1890_, 5, v___f_1885_);
v___x_1891_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_reflectBV_spec__5___redArg(v_g_1874_, v___f_1890_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg___boxed(lean_object* v_g_1892_, lean_object* v_unsatProver_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1892_, v_unsatProver_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(lean_object* v_00_u03b1_1904_, lean_object* v_g_1905_, lean_object* v_unsatProver_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(v_g_1905_, v_unsatProver_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___boxed(lean_object* v_00_u03b1_1917_, lean_object* v_g_1918_, lean_object* v_unsatProver_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection(v_00_u03b1_1917_, v_g_1918_, v_unsatProver_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
lean_dec(v_a_1925_);
lean_dec_ref(v_a_1924_);
lean_dec(v_a_1923_);
lean_dec_ref(v_a_1922_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(lean_object* v_mvarId_1930_, lean_object* v_val_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___redArg(v_mvarId_1930_, v_val_1931_, v___y_1937_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3___boxed(lean_object* v_mvarId_1942_, lean_object* v_val_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3(v_mvarId_1942_, v_val_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(lean_object* v_cls_1954_, lean_object* v_msg_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___redArg(v_cls_1954_, v_msg_1955_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5___boxed(lean_object* v_cls_1966_, lean_object* v_msg_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__5(v_cls_1966_, v_msg_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__13(lean_object* v_00_u03b1_1978_, lean_object* v_x_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__13___redArg(v_x_1979_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__13___boxed(lean_object* v_00_u03b1_1990_, lean_object* v_x_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__13(v_00_u03b1_1990_, v_x_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2(lean_object* v_00_u03b2_2002_, lean_object* v_m_2003_, lean_object* v_query_2004_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2___redArg(v_m_2003_, v_query_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2___boxed(lean_object* v_00_u03b2_2006_, lean_object* v_m_2007_, lean_object* v_query_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2(v_00_u03b2_2006_, v_m_2007_, v_query_2008_);
lean_dec(v_query_2008_);
lean_dec_ref(v_m_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3(lean_object* v_00_u03b2_2010_, lean_object* v_m_2011_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3___redArg(v_m_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2013_, lean_object* v_m_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3(v_00_u03b2_2013_, v_m_2014_);
lean_dec_ref(v_m_2014_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4(lean_object* v_as_2016_, lean_object* v_as_x27_2017_, lean_object* v_b_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___redArg(v_as_x27_2017_, v_b_2018_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4___boxed(lean_object* v_as_2021_, lean_object* v_as_x27_2022_, lean_object* v_b_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__4(v_as_2021_, v_as_x27_2022_, v_b_2023_, v_a_2024_);
lean_dec(v_as_x27_2022_);
lean_dec(v_as_2021_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6(lean_object* v_00_u03b2_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6___redArg(v_x_2027_, v_x_2028_, v_x_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12(lean_object* v_oldTraces_2031_, lean_object* v_data_2032_, lean_object* v_ref_2033_, lean_object* v_msg_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12___redArg(v_oldTraces_2031_, v_data_2032_, v_ref_2033_, v_msg_2034_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12___boxed(lean_object* v_oldTraces_2045_, lean_object* v_data_2046_, lean_object* v_ref_2047_, lean_object* v_msg_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__8_spec__12(v_oldTraces_2045_, v_data_2046_, v_ref_2047_, v_msg_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_2059_, lean_object* v_m_2060_, lean_object* v_query_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2_spec__5___redArg(v_m_2060_, v_query_2061_, v_x_2062_, v_x_2063_, v_x_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2067_, lean_object* v_m_2068_, lean_object* v_query_2069_, lean_object* v_x_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_, lean_object* v_x_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__2_spec__5(v_00_u03b2_2067_, v_m_2068_, v_query_2069_, v_x_2070_, v_x_2071_, v_x_2072_, v_x_2073_);
lean_dec(v_query_2069_);
lean_dec_ref(v_m_2068_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_2075_, lean_object* v_init_2076_, lean_object* v_b_2077_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7___redArg(v_init_2076_, v_b_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2079_, lean_object* v_init_2080_, lean_object* v_b_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7(v_00_u03b2_2079_, v_init_2080_, v_b_2081_);
lean_dec_ref(v_b_2081_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11(lean_object* v_00_u03b2_2083_, lean_object* v_x_2084_, size_t v_x_2085_, size_t v_x_2086_, lean_object* v_x_2087_, lean_object* v_x_2088_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___redArg(v_x_2084_, v_x_2085_, v_x_2086_, v_x_2087_, v_x_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11___boxed(lean_object* v_00_u03b2_2090_, lean_object* v_x_2091_, lean_object* v_x_2092_, lean_object* v_x_2093_, lean_object* v_x_2094_, lean_object* v_x_2095_){
_start:
{
size_t v_x_42369__boxed_2096_; size_t v_x_42370__boxed_2097_; lean_object* v_res_2098_; 
v_x_42369__boxed_2096_ = lean_unbox_usize(v_x_2092_);
lean_dec(v_x_2092_);
v_x_42370__boxed_2097_ = lean_unbox_usize(v_x_2093_);
lean_dec(v_x_2093_);
v_res_2098_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11(v_00_u03b2_2090_, v_x_2091_, v_x_42369__boxed_2096_, v_x_42370__boxed_2097_, v_x_2094_, v_x_2095_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7_spec__15(lean_object* v_00_u03b2_2099_, lean_object* v_b_2100_, lean_object* v_acc_2101_, lean_object* v_i_2102_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7_spec__15___redArg(v_b_2100_, v_acc_2101_, v_i_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7_spec__15___boxed(lean_object* v_00_u03b2_2104_, lean_object* v_b_2105_, lean_object* v_acc_2106_, lean_object* v_i_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__2_spec__3_spec__7_spec__15(v_00_u03b2_2104_, v_b_2105_, v_acc_2106_, v_i_2107_);
lean_dec_ref(v_b_2105_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__19(lean_object* v_00_u03b2_2109_, lean_object* v_n_2110_, lean_object* v_k_2111_, lean_object* v_v_2112_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__19___redArg(v_n_2110_, v_k_2111_, v_v_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__20(lean_object* v_00_u03b2_2114_, size_t v_depth_2115_, lean_object* v_keys_2116_, lean_object* v_vals_2117_, lean_object* v_heq_2118_, lean_object* v_i_2119_, lean_object* v_entries_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__20___redArg(v_depth_2115_, v_keys_2116_, v_vals_2117_, v_i_2119_, v_entries_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__20___boxed(lean_object* v_00_u03b2_2122_, lean_object* v_depth_2123_, lean_object* v_keys_2124_, lean_object* v_vals_2125_, lean_object* v_heq_2126_, lean_object* v_i_2127_, lean_object* v_entries_2128_){
_start:
{
size_t v_depth_boxed_2129_; lean_object* v_res_2130_; 
v_depth_boxed_2129_ = lean_unbox_usize(v_depth_2123_);
lean_dec(v_depth_2123_);
v_res_2130_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__20(v_00_u03b2_2122_, v_depth_boxed_2129_, v_keys_2124_, v_vals_2125_, v_heq_2126_, v_i_2127_, v_entries_2128_);
lean_dec_ref(v_vals_2125_);
lean_dec_ref(v_keys_2124_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__19_spec__21(lean_object* v_00_u03b2_2131_, lean_object* v_x_2132_, lean_object* v_x_2133_, lean_object* v_x_2134_, lean_object* v_x_2135_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_closeWithBVReflection_spec__3_spec__6_spec__11_spec__19_spec__21___redArg(v_x_2132_, v_x_2133_, v_x_2134_, v_x_2135_);
return v___x_2136_;
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
