// Lean compiler output
// Module: Lean.Meta.Diagnostics
// Imports: Lean.PrettyPrinter Lean.Meta.Basic Lean.Meta.Instances
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
extern lean_object* l_Lean_diagExt;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_log___at___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_collectAboveThreshold___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_subCounters___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_appendSection___closed__1;
static lean_object* l_Lean_Meta_reportDiag___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_lt___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_collectAboveThreshold___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_mkDiagSummary___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkDiagSummary___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_mkDiagSummary___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiagSummary_isEmpty___boxed(lean_object*);
lean_object* l___private_Init_GetElem_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_mkDiagSummary___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_mkDiagSummary___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedDiagSummary___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_mkDiagSummaryForUsedInstances___lambda__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiagSummary_isEmpty(lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_registerCoercion___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_subCounters___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUnfolded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_mkDiagSummary___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reportDiag___closed__17;
static lean_object* l_Lean_Meta_reportDiag___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiagSummary_max___default;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_appendSection___closed__3;
LEAN_EXPORT uint8_t l_Lean_Meta_mkDiagSummaryForUnfolded___lambda__1(lean_object*, uint8_t, lean_object*);
extern lean_object* l_instInhabitedNat;
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUsedInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_subCounters___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedDiagSummary;
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_collectAboveThreshold___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_isInstanceCore(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reportDiag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUnfolded___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_collectAboveThreshold___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_mkDiagSummary___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at_Lean_Meta_mkDiagSummary___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUnfolded(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_subCounters___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiagSummary_data___default;
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reportDiag___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_mkDiagSummary___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_collectAboveThreshold___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_subCounters___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_collectAboveThreshold___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_collectAboveThreshold___spec__6___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reportDiag___closed__2;
static lean_object* l_Lean_Meta_mkDiagSummary___closed__2;
static lean_object* l_Lean_Meta_reportDiag___closed__6;
static double l_Lean_Meta_appendSection___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_collectAboveThreshold___spec__6(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_mkDiagSummary___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_collectAboveThreshold___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_subCounters___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_subCounters___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__5;
lean_object* l_Lean_MessageData_ofConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_subCounters___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUnfoldedReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_collectAboveThreshold___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_collectAboveThreshold___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_subCounters___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reportDiag___closed__9;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_subCounters___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_subCounters___spec__3(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUsedInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_collectAboveThreshold___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendSection(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reportDiag___closed__5;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__4;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__8;
static lean_object* l_Lean_Meta_subCounters___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_appendSection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_collectAboveThreshold___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Kernel_instInhabitedDiagnostics;
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reportDiag___closed__4;
static lean_object* l_Lean_Meta_reportDiag___closed__15;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_collectAboveThreshold___spec__1(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__12;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_collectAboveThreshold___spec__4___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_collectAboveThreshold___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_collectAboveThreshold___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_mkDiagSummary___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_mkDiagSummary___spec__7___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__11;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUsedInstances___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_subCounters___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkDiagSummary___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_mkDiagSummary___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_mkDiagSummary___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reportDiag___closed__7;
static lean_object* l_Lean_Meta_reportDiag___closed__8;
extern lean_object* l_Lean_diagnostics_threshold;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__9;
static lean_object* l_Lean_Meta_reportDiag___closed__13;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__3;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_appendSection___closed__2;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_collectAboveThreshold___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_subCounters___spec__1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at_Lean_Meta_mkDiagSummary___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_mkDiagSummary___spec__5___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at_Lean_Meta_mkDiagSummary___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reportDiag___closed__10;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_subCounters___spec__2(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_mkDiagSummary___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_collectAboveThreshold___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reportDiag___closed__16;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_collectAboveThreshold___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1;
lean_object* l_Lean_isDiagnosticsEnabled(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_reportDiag___closed__1;
static lean_object* l_Lean_Meta_reportDiag___closed__12;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_subCounters___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_subCounters___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_collectAboveThreshold___spec__4___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = lean_apply_3(x_1, x_5, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_14;
goto _start;
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
lean_inc(x_1);
x_19 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_collectAboveThreshold___spec__3___rarg(x_1, x_18, x_5);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = 1;
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
x_5 = x_23;
goto _start;
}
}
default: 
{
size_t x_27; size_t x_28; 
x_27 = 1;
x_28 = lean_usize_add(x_3, x_27);
x_3 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_1);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_5);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_collectAboveThreshold___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_collectAboveThreshold___spec__4___rarg___boxed), 5, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_collectAboveThreshold___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
x_12 = lean_apply_3(x_1, x_6, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_18;
x_6 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_collectAboveThreshold___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_collectAboveThreshold___spec__5___rarg___boxed), 6, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_collectAboveThreshold___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_collectAboveThreshold___spec__4___rarg(x_1, x_4, x_11, x_12, x_3);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_collectAboveThreshold___spec__5___rarg(x_1, x_14, x_15, lean_box(0), x_16, x_3);
lean_dec(x_15);
lean_dec(x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_collectAboveThreshold___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_collectAboveThreshold___spec__3___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_collectAboveThreshold___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_collectAboveThreshold___spec__3___rarg(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_collectAboveThreshold___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_collectAboveThreshold___spec__2___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_collectAboveThreshold___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_apply_2(x_1, x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_collectAboveThreshold___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at_Lean_Meta_collectAboveThreshold___spec__1___rarg___lambda__1), 4, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_collectAboveThreshold___spec__2___rarg(x_3, x_6, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_collectAboveThreshold___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at_Lean_Meta_collectAboveThreshold___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_collectAboveThreshold___spec__6___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_9 = lean_nat_dec_lt(x_7, x_5);
lean_dec(x_5);
lean_dec(x_7);
x_10 = lean_box(x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
x_11 = lean_apply_2(x_1, x_4, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_collectAboveThreshold___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_Meta_collectAboveThreshold___spec__6___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_nat_dec_lt(x_3, x_4);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_3);
x_7 = l_Array_qpartition___rarg(x_2, x_5, x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_nat_dec_le(x_4, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_11 = l_Array_qsort_sort___at_Lean_Meta_collectAboveThreshold___spec__6___rarg(x_1, x_9, x_3, x_8);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_collectAboveThreshold___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_Meta_collectAboveThreshold___spec__6___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_nat_dec_lt(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_inc(x_6);
x_10 = lean_apply_1(x_2, x_6);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_push(x_4, x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = lean_nat_dec_lt(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc(x_15);
x_19 = lean_apply_1(x_2, x_15);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_array_push(x_4, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_collectAboveThreshold___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_collectAboveThreshold___rarg___lambda__1___boxed), 4, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
x_8 = l_Lean_Meta_collectAboveThreshold___rarg___closed__1;
x_9 = l_Lean_PersistentHashMap_forIn___at_Lean_Meta_collectAboveThreshold___spec__1___rarg(x_1, x_2, x_3, x_8, x_7);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_qsort_sort___at_Lean_Meta_collectAboveThreshold___spec__6___rarg(x_6, x_9, x_13, x_12);
lean_dec(x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_collectAboveThreshold___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_collectAboveThreshold___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_collectAboveThreshold___spec__4___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_collectAboveThreshold___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_collectAboveThreshold___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_collectAboveThreshold___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_collectAboveThreshold___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_collectAboveThreshold___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_forIn___at_Lean_Meta_collectAboveThreshold___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_collectAboveThreshold___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at_Lean_Meta_collectAboveThreshold___spec__6___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_collectAboveThreshold___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_subCounters___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_8, x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_uget(x_7, x_8);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
x_15 = lean_apply_3(x_6, x_10, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = 1;
x_21 = lean_usize_add(x_8, x_20);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_8 = x_21;
x_10 = x_19;
goto _start;
}
}
case 1:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
lean_inc(x_6);
x_24 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_subCounters___spec__3___rarg(x_1, x_2, lean_box(0), lean_box(0), lean_box(0), x_6, x_23, x_10);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; size_t x_29; size_t x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = 1;
x_30 = lean_usize_add(x_8, x_29);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_8 = x_30;
x_10 = x_28;
goto _start;
}
}
default: 
{
size_t x_32; size_t x_33; 
x_32 = 1;
x_33 = lean_usize_add(x_8, x_32);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_8 = x_33;
goto _start;
}
}
}
else
{
lean_object* x_35; 
lean_dec(x_6);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_10);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_subCounters___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_subCounters___spec__4___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_subCounters___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_7);
x_13 = lean_nat_dec_lt(x_10, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_10);
x_16 = lean_array_fget(x_8, x_10);
lean_inc(x_6);
x_17 = lean_apply_3(x_6, x_11, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_6);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_10, x_22);
lean_dec(x_10);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_9 = lean_box(0);
x_10 = x_23;
x_11 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_subCounters___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_subCounters___spec__5___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_subCounters___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_8);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_subCounters___spec__4___rarg(x_1, x_2, lean_box(0), lean_box(0), lean_box(0), x_6, x_9, x_16, x_17, x_8);
lean_dec(x_9);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_subCounters___spec__5___rarg(x_1, x_2, lean_box(0), lean_box(0), lean_box(0), x_6, x_19, x_20, lean_box(0), x_21, x_8);
lean_dec(x_20);
lean_dec(x_19);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_subCounters___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_subCounters___spec__3___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_subCounters___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_subCounters___spec__3___rarg(x_1, x_2, lean_box(0), lean_box(0), lean_box(0), x_4, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_subCounters___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_subCounters___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_subCounters___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at_Lean_Meta_collectAboveThreshold___spec__1___rarg___lambda__1), 4, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_subCounters___spec__2___rarg(x_1, x_2, x_3, x_6, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_subCounters___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at_Lean_Meta_subCounters___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_PersistentHashMap_find_x3f___rarg(x_1, x_2, x_3, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_PersistentHashMap_insert___rarg(x_1, x_2, x_5, x_6, x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_nat_sub(x_7, x_11);
lean_dec(x_11);
lean_dec(x_7);
x_13 = l_Lean_PersistentHashMap_insert___rarg(x_1, x_2, x_5, x_6, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Meta_subCounters___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_subCounters___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subCounters___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_Meta_subCounters___rarg___closed__2;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_subCounters___rarg___lambda__1), 5, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_4);
x_9 = l_Lean_PersistentHashMap_forIn___at_Lean_Meta_subCounters___spec__1___rarg(x_1, x_2, x_3, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subCounters(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_subCounters___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_subCounters___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_subCounters___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_subCounters___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_subCounters___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_subCounters___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_subCounters___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_subCounters___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_subCounters___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_subCounters___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_forIn___at_Lean_Meta_subCounters___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_DiagSummary_data___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_collectAboveThreshold___rarg___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiagSummary_max___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedDiagSummary___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_collectAboveThreshold___rarg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedDiagSummary() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedDiagSummary___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiagSummary_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Array_isEmpty___rarg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiagSummary_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_DiagSummary_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_mkDiagSummary___spec__5___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = lean_apply_3(x_1, x_5, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_14;
goto _start;
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
lean_inc(x_1);
x_19 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_mkDiagSummary___spec__4___rarg(x_1, x_18, x_5);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = 1;
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
x_5 = x_23;
goto _start;
}
}
default: 
{
size_t x_27; size_t x_28; 
x_27 = 1;
x_28 = lean_usize_add(x_3, x_27);
x_3 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_1);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_5);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_mkDiagSummary___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_mkDiagSummary___spec__5___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_mkDiagSummary___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_2, x_5);
x_11 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
x_12 = lean_apply_3(x_1, x_6, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_18;
x_6 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_mkDiagSummary___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_mkDiagSummary___spec__6___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_mkDiagSummary___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_mkDiagSummary___spec__5___rarg(x_1, x_4, x_11, x_12, x_3);
lean_dec(x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_mkDiagSummary___spec__6___rarg(x_1, x_14, x_15, lean_box(0), x_16, x_3);
lean_dec(x_15);
lean_dec(x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_mkDiagSummary___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_mkDiagSummary___spec__4___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_mkDiagSummary___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Meta_mkDiagSummary___spec__4___rarg(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_mkDiagSummary___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_apply_2(x_1, x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at_Lean_Meta_mkDiagSummary___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at_Lean_Meta_mkDiagSummary___spec__2___lambda__1), 4, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_mkDiagSummary___spec__3(x_1, x_4, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_mkDiagSummary___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_9 = lean_nat_dec_lt(x_7, x_5);
lean_dec(x_5);
lean_dec(x_7);
x_10 = lean_box(x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
x_11 = lean_apply_2(x_1, x_4, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_mkDiagSummary___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_Meta_mkDiagSummary___spec__7___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_nat_dec_lt(x_3, x_4);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_3);
x_7 = l_Array_qpartition___rarg(x_2, x_5, x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_nat_dec_le(x_4, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_11 = l_Array_qsort_sort___at_Lean_Meta_mkDiagSummary___spec__7(x_1, x_9, x_3, x_8);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at_Lean_Meta_mkDiagSummary___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_nat_dec_lt(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_inc(x_6);
x_10 = lean_apply_1(x_2, x_6);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_push(x_4, x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = lean_nat_dec_lt(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc(x_15);
x_19 = lean_apply_1(x_2, x_15);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_array_push(x_4, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at_Lean_Meta_mkDiagSummary___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_collectAboveThreshold___at_Lean_Meta_mkDiagSummary___spec__1___lambda__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Lean_Meta_collectAboveThreshold___rarg___closed__1;
x_7 = l_Lean_PersistentHashMap_forIn___at_Lean_Meta_mkDiagSummary___spec__2(x_1, x_6, x_5);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_qsort_sort___at_Lean_Meta_mkDiagSummary___spec__7(x_4, x_7, x_11, x_10);
lean_dec(x_10);
return x_12;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ↦ ", 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__6;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__7;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__2;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("  ", 2);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__10;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__11;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__2;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_mkConstWithLevelParams___at_Lean_Meta_registerCoercion___spec__1(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Array_isEmpty___rarg(x_4);
x_19 = l_Lean_MessageData_ofConst(x_16);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_14);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
if (x_18 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_23 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__8;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__4;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
x_28 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_push(x_4, x_29);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_4 = x_30;
x_9 = x_17;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
x_34 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__12;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_19);
x_36 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__4;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_22);
x_39 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__2;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_array_push(x_4, x_40);
x_42 = 1;
x_43 = lean_usize_add(x_3, x_42);
x_3 = x_43;
x_4 = x_41;
x_9 = x_17;
goto _start;
}
}
else
{
uint8_t x_45; 
lean_dec(x_14);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkDiagSummary___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics_threshold;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkDiagSummary___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_lt___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkDiagSummary___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedName;
x_2 = l_instInhabitedNat;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_5, 2);
x_9 = l_Lean_Meta_mkDiagSummary___closed__1;
x_10 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_8, x_9);
x_11 = l_Lean_Meta_mkDiagSummary___closed__2;
x_12 = l_Lean_Meta_collectAboveThreshold___at_Lean_Meta_mkDiagSummary___spec__1(x_1, x_10, x_2, x_11);
x_13 = l_Array_isEmpty___rarg(x_12);
if (x_13 == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_get_size(x_12);
x_15 = lean_usize_of_nat(x_14);
x_16 = 0;
x_17 = l_Lean_Meta_collectAboveThreshold___rarg___closed__1;
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8(x_12, x_15, x_16, x_17, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_14);
lean_dec(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
x_23 = l_Lean_Meta_mkDiagSummary___closed__3;
x_24 = l___private_Init_GetElem_0__outOfBounds___rarg(x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_18, 0, x_26);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_array_fget(x_12, x_21);
lean_dec(x_12);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_14);
lean_dec(x_14);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_12);
x_34 = l_Lean_Meta_mkDiagSummary___closed__3;
x_35 = l___private_Init_GetElem_0__outOfBounds___rarg(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_fget(x_12, x_32);
lean_dec(x_12);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_31);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_14);
lean_dec(x_12);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
return x_18;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_18, 0);
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_18);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_12);
x_47 = l_Lean_Meta_instInhabitedDiagSummary___closed__1;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_mkDiagSummary___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_mkDiagSummary___spec__5___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_mkDiagSummary___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Meta_mkDiagSummary___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Meta_mkDiagSummary___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at_Lean_Meta_mkDiagSummary___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_collectAboveThreshold___at_Lean_Meta_mkDiagSummary___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_collectAboveThreshold___at_Lean_Meta_mkDiagSummary___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummary___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkDiagSummary(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_mkDiagSummaryForUnfolded___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_get_reducibility_status(x_1, x_3);
x_5 = lean_box(x_4);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = l_Lean_Meta_isInstanceCore(x_1, x_3);
lean_dec(x_1);
if (x_6 == 0)
{
if (x_2 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
else
{
return x_2;
}
}
else
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUnfolded(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_mkDiagSummaryForUnfolded___lambda__1___boxed), 3, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_mkDiagSummary(x_1, x_13, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUnfolded___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_mkDiagSummaryForUnfolded___lambda__1(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUnfolded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_mkDiagSummaryForUnfolded(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_get_reducibility_status(x_1, x_2);
x_4 = lean_box(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUnfoldedReducible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_Lean_Meta_mkDiagSummary(x_1, x_11, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUnfoldedReducible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_mkDiagSummaryForUnfoldedReducible(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_mkDiagSummaryForUsedInstances___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkDiagSummaryForUsedInstances___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUsedInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_st_ref_get(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 4);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1;
x_12 = l_Lean_Meta_mkDiagSummary(x_10, x_11, x_1, x_2, x_3, x_4, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUsedInstances___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_mkDiagSummaryForUsedInstances___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDiagSummaryForUsedInstances___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkDiagSummaryForUsedInstances(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_appendSection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" (max: ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_appendSection___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", num: ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_appendSection___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("):", 2);
return x_1;
}
}
static double _init_l_Lean_Meta_appendSection___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendSection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Meta_DiagSummary_isEmpty(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; double x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_6 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__1;
x_7 = lean_string_append(x_6, x_3);
x_8 = l_Lean_Meta_appendSection___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = l___private_Init_Data_Repr_0__Nat_reprFast(x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
x_13 = l_Lean_Meta_appendSection___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_array_get_size(x_15);
x_17 = l___private_Init_Data_Repr_0__Nat_reprFast(x_16);
x_18 = lean_string_append(x_14, x_17);
lean_dec(x_17);
x_19 = l_Lean_Meta_appendSection___closed__3;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_Meta_appendSection___closed__4;
x_22 = 1;
x_23 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set_float(x_23, sizeof(void*)*2, x_21);
lean_ctor_set_float(x_23, sizeof(void*)*2 + 8, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 16, x_22);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_20);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_15);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendSection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_appendSection(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduction", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reportDiag___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unfolded declarations", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unfolded instances", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unfolded reducible declarations", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type_class", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reportDiag___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("used instances", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("def_eq", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reportDiag___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("heuristic for solving `f a =\?= f b`", 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("kernel", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reportDiag___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("use `set_option diagnostics.threshold <num>` to control threshold for reporting counters", 88);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reportDiag___closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_reportDiag___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_reportDiag___closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reportDiag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_isDiagnosticsEnabled(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_st_ref_get(x_2, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 4);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 0;
lean_inc(x_20);
x_22 = l_Lean_Meta_mkDiagSummaryForUnfolded(x_20, x_21, x_1, x_2, x_3, x_4, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
lean_inc(x_20);
x_26 = l_Lean_Meta_mkDiagSummaryForUnfolded(x_20, x_25, x_1, x_2, x_3, x_4, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_mkDiagSummaryForUnfoldedReducible(x_20, x_1, x_2, x_3, x_4, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_2, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 4);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1;
x_38 = l_Lean_Meta_mkDiagSummary(x_36, x_37, x_1, x_2, x_3, x_4, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_mkDiagSummaryForUsedInstances(x_1, x_2, x_3, x_4, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_st_ref_get(x_4, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Kernel_instInhabitedDiagnostics;
x_49 = l_Lean_Meta_reportDiag___closed__1;
x_50 = l_Lean_EnvExtension_getState___rarg(x_48, x_49, x_47);
lean_dec(x_47);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_Lean_Meta_mkDiagSummary(x_51, x_37, x_1, x_2, x_3, x_4, x_46);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = l_Lean_Meta_DiagSummary_isEmpty(x_23);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
lean_free_object(x_52);
x_57 = l_Lean_MessageData_nil;
x_58 = l_Lean_Meta_reportDiag___closed__3;
x_59 = l_Lean_Meta_reportDiag___closed__4;
x_60 = l_Lean_Meta_appendSection(x_57, x_58, x_59, x_23);
x_61 = l_Lean_Meta_reportDiag___closed__5;
x_62 = l_Lean_Meta_appendSection(x_60, x_58, x_61, x_27);
x_63 = l_Lean_Meta_reportDiag___closed__6;
x_64 = l_Lean_Meta_appendSection(x_62, x_58, x_63, x_30);
x_65 = l_Lean_Meta_reportDiag___closed__8;
x_66 = l_Lean_Meta_reportDiag___closed__9;
x_67 = l_Lean_Meta_appendSection(x_64, x_65, x_66, x_42);
x_68 = l_Lean_Meta_reportDiag___closed__11;
x_69 = l_Lean_Meta_reportDiag___closed__12;
x_70 = l_Lean_Meta_appendSection(x_67, x_68, x_69, x_39);
x_71 = l_Lean_Meta_reportDiag___closed__14;
x_72 = l_Lean_Meta_appendSection(x_70, x_71, x_59, x_54);
x_73 = l_Lean_Meta_reportDiag___closed__17;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = 0;
x_76 = l_Lean_log___at___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___spec__6(x_74, x_75, x_1, x_2, x_3, x_4, x_55);
return x_76;
}
else
{
uint8_t x_77; 
x_77 = l_Lean_Meta_DiagSummary_isEmpty(x_27);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
lean_free_object(x_52);
x_78 = l_Lean_MessageData_nil;
x_79 = l_Lean_Meta_reportDiag___closed__3;
x_80 = l_Lean_Meta_reportDiag___closed__4;
x_81 = l_Lean_Meta_appendSection(x_78, x_79, x_80, x_23);
x_82 = l_Lean_Meta_reportDiag___closed__5;
x_83 = l_Lean_Meta_appendSection(x_81, x_79, x_82, x_27);
x_84 = l_Lean_Meta_reportDiag___closed__6;
x_85 = l_Lean_Meta_appendSection(x_83, x_79, x_84, x_30);
x_86 = l_Lean_Meta_reportDiag___closed__8;
x_87 = l_Lean_Meta_reportDiag___closed__9;
x_88 = l_Lean_Meta_appendSection(x_85, x_86, x_87, x_42);
x_89 = l_Lean_Meta_reportDiag___closed__11;
x_90 = l_Lean_Meta_reportDiag___closed__12;
x_91 = l_Lean_Meta_appendSection(x_88, x_89, x_90, x_39);
x_92 = l_Lean_Meta_reportDiag___closed__14;
x_93 = l_Lean_Meta_appendSection(x_91, x_92, x_80, x_54);
x_94 = l_Lean_Meta_reportDiag___closed__17;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = 0;
x_97 = l_Lean_log___at___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___spec__6(x_95, x_96, x_1, x_2, x_3, x_4, x_55);
return x_97;
}
else
{
uint8_t x_98; 
x_98 = l_Lean_Meta_DiagSummary_isEmpty(x_30);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; 
lean_free_object(x_52);
x_99 = l_Lean_MessageData_nil;
x_100 = l_Lean_Meta_reportDiag___closed__3;
x_101 = l_Lean_Meta_reportDiag___closed__4;
x_102 = l_Lean_Meta_appendSection(x_99, x_100, x_101, x_23);
x_103 = l_Lean_Meta_reportDiag___closed__5;
x_104 = l_Lean_Meta_appendSection(x_102, x_100, x_103, x_27);
x_105 = l_Lean_Meta_reportDiag___closed__6;
x_106 = l_Lean_Meta_appendSection(x_104, x_100, x_105, x_30);
x_107 = l_Lean_Meta_reportDiag___closed__8;
x_108 = l_Lean_Meta_reportDiag___closed__9;
x_109 = l_Lean_Meta_appendSection(x_106, x_107, x_108, x_42);
x_110 = l_Lean_Meta_reportDiag___closed__11;
x_111 = l_Lean_Meta_reportDiag___closed__12;
x_112 = l_Lean_Meta_appendSection(x_109, x_110, x_111, x_39);
x_113 = l_Lean_Meta_reportDiag___closed__14;
x_114 = l_Lean_Meta_appendSection(x_112, x_113, x_101, x_54);
x_115 = l_Lean_Meta_reportDiag___closed__17;
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = 0;
x_118 = l_Lean_log___at___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___spec__6(x_116, x_117, x_1, x_2, x_3, x_4, x_55);
return x_118;
}
else
{
uint8_t x_119; 
x_119 = l_Lean_Meta_DiagSummary_isEmpty(x_39);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
lean_free_object(x_52);
x_120 = l_Lean_MessageData_nil;
x_121 = l_Lean_Meta_reportDiag___closed__3;
x_122 = l_Lean_Meta_reportDiag___closed__4;
x_123 = l_Lean_Meta_appendSection(x_120, x_121, x_122, x_23);
x_124 = l_Lean_Meta_reportDiag___closed__5;
x_125 = l_Lean_Meta_appendSection(x_123, x_121, x_124, x_27);
x_126 = l_Lean_Meta_reportDiag___closed__6;
x_127 = l_Lean_Meta_appendSection(x_125, x_121, x_126, x_30);
x_128 = l_Lean_Meta_reportDiag___closed__8;
x_129 = l_Lean_Meta_reportDiag___closed__9;
x_130 = l_Lean_Meta_appendSection(x_127, x_128, x_129, x_42);
x_131 = l_Lean_Meta_reportDiag___closed__11;
x_132 = l_Lean_Meta_reportDiag___closed__12;
x_133 = l_Lean_Meta_appendSection(x_130, x_131, x_132, x_39);
x_134 = l_Lean_Meta_reportDiag___closed__14;
x_135 = l_Lean_Meta_appendSection(x_133, x_134, x_122, x_54);
x_136 = l_Lean_Meta_reportDiag___closed__17;
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = 0;
x_139 = l_Lean_log___at___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___spec__6(x_137, x_138, x_1, x_2, x_3, x_4, x_55);
return x_139;
}
else
{
uint8_t x_140; 
x_140 = l_Lean_Meta_DiagSummary_isEmpty(x_42);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; 
lean_free_object(x_52);
x_141 = l_Lean_MessageData_nil;
x_142 = l_Lean_Meta_reportDiag___closed__3;
x_143 = l_Lean_Meta_reportDiag___closed__4;
x_144 = l_Lean_Meta_appendSection(x_141, x_142, x_143, x_23);
x_145 = l_Lean_Meta_reportDiag___closed__5;
x_146 = l_Lean_Meta_appendSection(x_144, x_142, x_145, x_27);
x_147 = l_Lean_Meta_reportDiag___closed__6;
x_148 = l_Lean_Meta_appendSection(x_146, x_142, x_147, x_30);
x_149 = l_Lean_Meta_reportDiag___closed__8;
x_150 = l_Lean_Meta_reportDiag___closed__9;
x_151 = l_Lean_Meta_appendSection(x_148, x_149, x_150, x_42);
x_152 = l_Lean_Meta_reportDiag___closed__11;
x_153 = l_Lean_Meta_reportDiag___closed__12;
x_154 = l_Lean_Meta_appendSection(x_151, x_152, x_153, x_39);
x_155 = l_Lean_Meta_reportDiag___closed__14;
x_156 = l_Lean_Meta_appendSection(x_154, x_155, x_143, x_54);
x_157 = l_Lean_Meta_reportDiag___closed__17;
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = 0;
x_160 = l_Lean_log___at___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___spec__6(x_158, x_159, x_1, x_2, x_3, x_4, x_55);
return x_160;
}
else
{
lean_object* x_161; 
lean_dec(x_54);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_box(0);
lean_ctor_set(x_52, 0, x_161);
return x_52;
}
}
}
}
}
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = lean_ctor_get(x_52, 0);
x_163 = lean_ctor_get(x_52, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_52);
x_164 = l_Lean_Meta_DiagSummary_isEmpty(x_23);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; 
x_165 = l_Lean_MessageData_nil;
x_166 = l_Lean_Meta_reportDiag___closed__3;
x_167 = l_Lean_Meta_reportDiag___closed__4;
x_168 = l_Lean_Meta_appendSection(x_165, x_166, x_167, x_23);
x_169 = l_Lean_Meta_reportDiag___closed__5;
x_170 = l_Lean_Meta_appendSection(x_168, x_166, x_169, x_27);
x_171 = l_Lean_Meta_reportDiag___closed__6;
x_172 = l_Lean_Meta_appendSection(x_170, x_166, x_171, x_30);
x_173 = l_Lean_Meta_reportDiag___closed__8;
x_174 = l_Lean_Meta_reportDiag___closed__9;
x_175 = l_Lean_Meta_appendSection(x_172, x_173, x_174, x_42);
x_176 = l_Lean_Meta_reportDiag___closed__11;
x_177 = l_Lean_Meta_reportDiag___closed__12;
x_178 = l_Lean_Meta_appendSection(x_175, x_176, x_177, x_39);
x_179 = l_Lean_Meta_reportDiag___closed__14;
x_180 = l_Lean_Meta_appendSection(x_178, x_179, x_167, x_162);
x_181 = l_Lean_Meta_reportDiag___closed__17;
x_182 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = 0;
x_184 = l_Lean_log___at___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___spec__6(x_182, x_183, x_1, x_2, x_3, x_4, x_163);
return x_184;
}
else
{
uint8_t x_185; 
x_185 = l_Lean_Meta_DiagSummary_isEmpty(x_27);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; 
x_186 = l_Lean_MessageData_nil;
x_187 = l_Lean_Meta_reportDiag___closed__3;
x_188 = l_Lean_Meta_reportDiag___closed__4;
x_189 = l_Lean_Meta_appendSection(x_186, x_187, x_188, x_23);
x_190 = l_Lean_Meta_reportDiag___closed__5;
x_191 = l_Lean_Meta_appendSection(x_189, x_187, x_190, x_27);
x_192 = l_Lean_Meta_reportDiag___closed__6;
x_193 = l_Lean_Meta_appendSection(x_191, x_187, x_192, x_30);
x_194 = l_Lean_Meta_reportDiag___closed__8;
x_195 = l_Lean_Meta_reportDiag___closed__9;
x_196 = l_Lean_Meta_appendSection(x_193, x_194, x_195, x_42);
x_197 = l_Lean_Meta_reportDiag___closed__11;
x_198 = l_Lean_Meta_reportDiag___closed__12;
x_199 = l_Lean_Meta_appendSection(x_196, x_197, x_198, x_39);
x_200 = l_Lean_Meta_reportDiag___closed__14;
x_201 = l_Lean_Meta_appendSection(x_199, x_200, x_188, x_162);
x_202 = l_Lean_Meta_reportDiag___closed__17;
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = 0;
x_205 = l_Lean_log___at___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___spec__6(x_203, x_204, x_1, x_2, x_3, x_4, x_163);
return x_205;
}
else
{
uint8_t x_206; 
x_206 = l_Lean_Meta_DiagSummary_isEmpty(x_30);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; 
x_207 = l_Lean_MessageData_nil;
x_208 = l_Lean_Meta_reportDiag___closed__3;
x_209 = l_Lean_Meta_reportDiag___closed__4;
x_210 = l_Lean_Meta_appendSection(x_207, x_208, x_209, x_23);
x_211 = l_Lean_Meta_reportDiag___closed__5;
x_212 = l_Lean_Meta_appendSection(x_210, x_208, x_211, x_27);
x_213 = l_Lean_Meta_reportDiag___closed__6;
x_214 = l_Lean_Meta_appendSection(x_212, x_208, x_213, x_30);
x_215 = l_Lean_Meta_reportDiag___closed__8;
x_216 = l_Lean_Meta_reportDiag___closed__9;
x_217 = l_Lean_Meta_appendSection(x_214, x_215, x_216, x_42);
x_218 = l_Lean_Meta_reportDiag___closed__11;
x_219 = l_Lean_Meta_reportDiag___closed__12;
x_220 = l_Lean_Meta_appendSection(x_217, x_218, x_219, x_39);
x_221 = l_Lean_Meta_reportDiag___closed__14;
x_222 = l_Lean_Meta_appendSection(x_220, x_221, x_209, x_162);
x_223 = l_Lean_Meta_reportDiag___closed__17;
x_224 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = 0;
x_226 = l_Lean_log___at___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___spec__6(x_224, x_225, x_1, x_2, x_3, x_4, x_163);
return x_226;
}
else
{
uint8_t x_227; 
x_227 = l_Lean_Meta_DiagSummary_isEmpty(x_39);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; 
x_228 = l_Lean_MessageData_nil;
x_229 = l_Lean_Meta_reportDiag___closed__3;
x_230 = l_Lean_Meta_reportDiag___closed__4;
x_231 = l_Lean_Meta_appendSection(x_228, x_229, x_230, x_23);
x_232 = l_Lean_Meta_reportDiag___closed__5;
x_233 = l_Lean_Meta_appendSection(x_231, x_229, x_232, x_27);
x_234 = l_Lean_Meta_reportDiag___closed__6;
x_235 = l_Lean_Meta_appendSection(x_233, x_229, x_234, x_30);
x_236 = l_Lean_Meta_reportDiag___closed__8;
x_237 = l_Lean_Meta_reportDiag___closed__9;
x_238 = l_Lean_Meta_appendSection(x_235, x_236, x_237, x_42);
x_239 = l_Lean_Meta_reportDiag___closed__11;
x_240 = l_Lean_Meta_reportDiag___closed__12;
x_241 = l_Lean_Meta_appendSection(x_238, x_239, x_240, x_39);
x_242 = l_Lean_Meta_reportDiag___closed__14;
x_243 = l_Lean_Meta_appendSection(x_241, x_242, x_230, x_162);
x_244 = l_Lean_Meta_reportDiag___closed__17;
x_245 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = 0;
x_247 = l_Lean_log___at___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___spec__6(x_245, x_246, x_1, x_2, x_3, x_4, x_163);
return x_247;
}
else
{
uint8_t x_248; 
x_248 = l_Lean_Meta_DiagSummary_isEmpty(x_42);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; 
x_249 = l_Lean_MessageData_nil;
x_250 = l_Lean_Meta_reportDiag___closed__3;
x_251 = l_Lean_Meta_reportDiag___closed__4;
x_252 = l_Lean_Meta_appendSection(x_249, x_250, x_251, x_23);
x_253 = l_Lean_Meta_reportDiag___closed__5;
x_254 = l_Lean_Meta_appendSection(x_252, x_250, x_253, x_27);
x_255 = l_Lean_Meta_reportDiag___closed__6;
x_256 = l_Lean_Meta_appendSection(x_254, x_250, x_255, x_30);
x_257 = l_Lean_Meta_reportDiag___closed__8;
x_258 = l_Lean_Meta_reportDiag___closed__9;
x_259 = l_Lean_Meta_appendSection(x_256, x_257, x_258, x_42);
x_260 = l_Lean_Meta_reportDiag___closed__11;
x_261 = l_Lean_Meta_reportDiag___closed__12;
x_262 = l_Lean_Meta_appendSection(x_259, x_260, x_261, x_39);
x_263 = l_Lean_Meta_reportDiag___closed__14;
x_264 = l_Lean_Meta_appendSection(x_262, x_263, x_251, x_162);
x_265 = l_Lean_Meta_reportDiag___closed__17;
x_266 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
x_267 = 0;
x_268 = l_Lean_log___at___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___spec__6(x_266, x_267, x_1, x_2, x_3, x_4, x_163);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_162);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_269 = lean_box(0);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_163);
return x_270;
}
}
}
}
}
}
}
else
{
uint8_t x_271; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_271 = !lean_is_exclusive(x_52);
if (x_271 == 0)
{
return x_52;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_52, 0);
x_273 = lean_ctor_get(x_52, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_52);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
else
{
uint8_t x_275; 
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_275 = !lean_is_exclusive(x_41);
if (x_275 == 0)
{
return x_41;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_41, 0);
x_277 = lean_ctor_get(x_41, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_41);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_279 = !lean_is_exclusive(x_38);
if (x_279 == 0)
{
return x_38;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_38, 0);
x_281 = lean_ctor_get(x_38, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_38);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_283 = !lean_is_exclusive(x_29);
if (x_283 == 0)
{
return x_29;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_29, 0);
x_285 = lean_ctor_get(x_29, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_29);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
else
{
uint8_t x_287; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_287 = !lean_is_exclusive(x_26);
if (x_287 == 0)
{
return x_26;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_26, 0);
x_289 = lean_ctor_get(x_26, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_26);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
else
{
uint8_t x_291; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_291 = !lean_is_exclusive(x_22);
if (x_291 == 0)
{
return x_22;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_22, 0);
x_293 = lean_ctor_get(x_22, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_22);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
}
}
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Instances(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Diagnostics(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Instances(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_collectAboveThreshold___rarg___closed__1 = _init_l_Lean_Meta_collectAboveThreshold___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_collectAboveThreshold___rarg___closed__1);
l_Lean_Meta_subCounters___rarg___closed__1 = _init_l_Lean_Meta_subCounters___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_subCounters___rarg___closed__1);
l_Lean_Meta_subCounters___rarg___closed__2 = _init_l_Lean_Meta_subCounters___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_subCounters___rarg___closed__2);
l_Lean_Meta_DiagSummary_data___default = _init_l_Lean_Meta_DiagSummary_data___default();
lean_mark_persistent(l_Lean_Meta_DiagSummary_data___default);
l_Lean_Meta_DiagSummary_max___default = _init_l_Lean_Meta_DiagSummary_max___default();
lean_mark_persistent(l_Lean_Meta_DiagSummary_max___default);
l_Lean_Meta_instInhabitedDiagSummary___closed__1 = _init_l_Lean_Meta_instInhabitedDiagSummary___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedDiagSummary___closed__1);
l_Lean_Meta_instInhabitedDiagSummary = _init_l_Lean_Meta_instInhabitedDiagSummary();
lean_mark_persistent(l_Lean_Meta_instInhabitedDiagSummary);
l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__10);
l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__11 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__11);
l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__12 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__12();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_mkDiagSummary___spec__8___closed__12);
l_Lean_Meta_mkDiagSummary___closed__1 = _init_l_Lean_Meta_mkDiagSummary___closed__1();
lean_mark_persistent(l_Lean_Meta_mkDiagSummary___closed__1);
l_Lean_Meta_mkDiagSummary___closed__2 = _init_l_Lean_Meta_mkDiagSummary___closed__2();
lean_mark_persistent(l_Lean_Meta_mkDiagSummary___closed__2);
l_Lean_Meta_mkDiagSummary___closed__3 = _init_l_Lean_Meta_mkDiagSummary___closed__3();
lean_mark_persistent(l_Lean_Meta_mkDiagSummary___closed__3);
l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1 = _init_l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1();
lean_mark_persistent(l_Lean_Meta_mkDiagSummaryForUsedInstances___closed__1);
l_Lean_Meta_appendSection___closed__1 = _init_l_Lean_Meta_appendSection___closed__1();
lean_mark_persistent(l_Lean_Meta_appendSection___closed__1);
l_Lean_Meta_appendSection___closed__2 = _init_l_Lean_Meta_appendSection___closed__2();
lean_mark_persistent(l_Lean_Meta_appendSection___closed__2);
l_Lean_Meta_appendSection___closed__3 = _init_l_Lean_Meta_appendSection___closed__3();
lean_mark_persistent(l_Lean_Meta_appendSection___closed__3);
l_Lean_Meta_appendSection___closed__4 = _init_l_Lean_Meta_appendSection___closed__4();
l_Lean_Meta_reportDiag___closed__1 = _init_l_Lean_Meta_reportDiag___closed__1();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__1);
l_Lean_Meta_reportDiag___closed__2 = _init_l_Lean_Meta_reportDiag___closed__2();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__2);
l_Lean_Meta_reportDiag___closed__3 = _init_l_Lean_Meta_reportDiag___closed__3();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__3);
l_Lean_Meta_reportDiag___closed__4 = _init_l_Lean_Meta_reportDiag___closed__4();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__4);
l_Lean_Meta_reportDiag___closed__5 = _init_l_Lean_Meta_reportDiag___closed__5();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__5);
l_Lean_Meta_reportDiag___closed__6 = _init_l_Lean_Meta_reportDiag___closed__6();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__6);
l_Lean_Meta_reportDiag___closed__7 = _init_l_Lean_Meta_reportDiag___closed__7();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__7);
l_Lean_Meta_reportDiag___closed__8 = _init_l_Lean_Meta_reportDiag___closed__8();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__8);
l_Lean_Meta_reportDiag___closed__9 = _init_l_Lean_Meta_reportDiag___closed__9();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__9);
l_Lean_Meta_reportDiag___closed__10 = _init_l_Lean_Meta_reportDiag___closed__10();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__10);
l_Lean_Meta_reportDiag___closed__11 = _init_l_Lean_Meta_reportDiag___closed__11();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__11);
l_Lean_Meta_reportDiag___closed__12 = _init_l_Lean_Meta_reportDiag___closed__12();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__12);
l_Lean_Meta_reportDiag___closed__13 = _init_l_Lean_Meta_reportDiag___closed__13();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__13);
l_Lean_Meta_reportDiag___closed__14 = _init_l_Lean_Meta_reportDiag___closed__14();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__14);
l_Lean_Meta_reportDiag___closed__15 = _init_l_Lean_Meta_reportDiag___closed__15();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__15);
l_Lean_Meta_reportDiag___closed__16 = _init_l_Lean_Meta_reportDiag___closed__16();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__16);
l_Lean_Meta_reportDiag___closed__17 = _init_l_Lean_Meta_reportDiag___closed__17();
lean_mark_persistent(l_Lean_Meta_reportDiag___closed__17);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
