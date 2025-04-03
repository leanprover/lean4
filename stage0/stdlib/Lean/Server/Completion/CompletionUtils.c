// Lean compiler output
// Module: Lean.Server.Completion.CompletionUtils
// Imports: Init.Prelude Lean.Meta.WHNF
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
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureParentInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Server_Completion_minimizeGlobalIdentifierInContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__10(lean_object*, lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__5;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_mergeStructureResolutionOrders___spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__27(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__9(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__13(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_unfoldeDefinitionGuarded_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(lean_object*, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(lean_object*, lean_object*, size_t, size_t);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__11(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__19(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Structure_0__Lean_setStructureResolutionOrder___spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(lean_object*, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_erase___at_Lean_getAllParentStructures___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at_Lean_Environment_realizeConst___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__18(size_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24(lean_object*, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__1;
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_structureResolutionExt;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object*, lean_object*);
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__2;
lean_object* l_Array_eraseReps___at_Lean_mergeStructureResolutionOrders___spec__7(lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15___closed__1;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Server_Completion_minimizeGlobalIdentifierInContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedName;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mergeStructureResolutionOrders___spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__14(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__20(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_emptyWithCapacity(lean_object*, lean_object*);
lean_object* l_Array_insertIdx_loop___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_minimizeGlobalIdentifierInContext_shortenIn(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_minimizeGlobalIdentifierInContext_shortenIn(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = l_Lean_Name_isPrefixOf(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Name_getPrefix(x_2);
lean_dec(x_2);
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Name_replacePrefix(x_1, x_2, x_6);
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Server_Completion_minimizeGlobalIdentifierInContext___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_2);
x_12 = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext_shortenIn(x_2, x_10);
x_13 = l_List_elem___at_Lean_Environment_realizeConst___spec__5(x_12, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Name_getNumParts(x_12);
x_15 = l_Lean_Name_getNumParts(x_6);
x_16 = lean_nat_dec_lt(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_dec(x_12);
x_5 = x_9;
x_7 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_6);
x_5 = x_9;
x_6 = x_12;
x_7 = lean_box(0);
goto _start;
}
}
else
{
lean_dec(x_12);
x_5 = x_9;
x_7 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_name_eq(x_22, x_2);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_21);
x_5 = x_20;
x_7 = lean_box(0);
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = l_Lean_Name_getNumParts(x_21);
x_26 = l_Lean_Name_getNumParts(x_6);
x_27 = lean_nat_dec_lt(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_dec(x_21);
x_5 = x_20;
x_7 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_6);
x_5 = x_20;
x_6 = x_21;
x_7 = lean_box(0);
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_4 = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext_shortenIn(x_3, x_1);
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = l_List_forIn_x27_loop___at_Lean_Server_Completion_minimizeGlobalIdentifierInContext___spec__1(x_2, x_3, x_5, x_2, x_2, x_4, lean_box(0));
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Server_Completion_minimizeGlobalIdentifierInContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at_Lean_Server_Completion_minimizeGlobalIdentifierInContext___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_unfoldeDefinitionGuarded_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Exception_isInterrupt(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Exception_isRuntime(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_box(0);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
return x_8;
}
}
else
{
return x_8;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = l_Lean_Exception_isInterrupt(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Exception_isRuntime(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = 1;
x_16 = l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3(x_12, x_15, x_4, x_5, x_6, x_7, x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_14, x_2, x_19);
x_2 = x_21;
x_3 = x_22;
x_9 = x_18;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Array_toSubarray___rarg(x_6, x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
size_t x_14; size_t x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_10);
x_18 = lean_nat_dec_le(x_12, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = lean_nat_dec_lt(x_11, x_17);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
goto _start;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(x_1, x_10, x_23, x_24);
lean_dec(x_10);
if (x_25 == 0)
{
size_t x_26; size_t x_27; 
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
}
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
lean_dec(x_17);
x_30 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_31 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_32 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8(x_1, x_10, x_30, x_31);
lean_dec(x_10);
if (x_32 == 0)
{
size_t x_33; size_t x_34; 
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
x_36 = 1;
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
x_37 = 0;
return x_37;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Array_toSubarray___rarg(x_6, x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
size_t x_14; size_t x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_10);
x_18 = lean_nat_dec_le(x_12, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = lean_nat_dec_lt(x_11, x_17);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
goto _start;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(x_1, x_10, x_23, x_24);
lean_dec(x_10);
if (x_25 == 0)
{
size_t x_26; size_t x_27; 
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
}
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
lean_dec(x_17);
x_30 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_31 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_32 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8(x_1, x_10, x_30, x_31);
lean_dec(x_10);
if (x_32 == 0)
{
size_t x_33; size_t x_34; 
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
x_36 = 1;
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
x_37 = 0;
return x_37;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Array_toSubarray___rarg(x_6, x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
size_t x_14; size_t x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_10);
x_18 = lean_nat_dec_le(x_12, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = lean_nat_dec_lt(x_11, x_17);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
goto _start;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__11(x_1, x_10, x_23, x_24);
lean_dec(x_10);
if (x_25 == 0)
{
size_t x_26; size_t x_27; 
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
}
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
lean_dec(x_17);
x_30 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_31 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_32 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12(x_1, x_10, x_30, x_31);
lean_dec(x_10);
if (x_32 == 0)
{
size_t x_33; size_t x_34; 
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
x_36 = 1;
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
x_37 = 0;
return x_37;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__14(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Array_toSubarray___rarg(x_6, x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
size_t x_14; size_t x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_10);
x_18 = lean_nat_dec_le(x_12, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = lean_nat_dec_lt(x_11, x_17);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
goto _start;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__11(x_1, x_10, x_23, x_24);
lean_dec(x_10);
if (x_25 == 0)
{
size_t x_26; size_t x_27; 
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
}
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
lean_dec(x_17);
x_30 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_31 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_32 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12(x_1, x_10, x_30, x_31);
lean_dec(x_10);
if (x_32 == 0)
{
size_t x_33; size_t x_34; 
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
x_36 = 1;
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
x_37 = 0;
return x_37;
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Array_emptyWithCapacity(lean_box(0), x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_nat_dec_lt(x_8, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_34; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_7);
x_20 = l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15___closed__1;
x_21 = lean_array_get(x_20, x_1, x_8);
x_22 = l_Lean_instInhabitedName;
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get(x_22, x_21, x_23);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_1);
x_62 = l_Array_toSubarray___rarg(x_1, x_23, x_8);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 2);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_nat_dec_lt(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
x_67 = lean_box(0);
x_34 = x_67;
goto block_61;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_array_get_size(x_63);
x_69 = lean_nat_dec_le(x_65, x_68);
if (x_69 == 0)
{
uint8_t x_70; 
lean_dec(x_65);
x_70 = lean_nat_dec_lt(x_64, x_68);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_68);
lean_dec(x_64);
lean_dec(x_63);
x_71 = lean_box(0);
x_34 = x_71;
goto block_61;
}
else
{
size_t x_72; size_t x_73; uint8_t x_74; 
x_72 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_73 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_74 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__13(x_24, x_63, x_72, x_73);
lean_dec(x_63);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_box(0);
x_34 = x_75;
goto block_61;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_24);
x_76 = lean_ctor_get(x_6, 2);
x_77 = lean_nat_add(x_8, x_76);
lean_dec(x_8);
lean_inc(x_2);
{
lean_object* _tmp_6 = x_2;
lean_object* _tmp_7 = x_77;
lean_object* _tmp_8 = lean_box(0);
lean_object* _tmp_9 = lean_box(0);
x_7 = _tmp_6;
x_8 = _tmp_7;
x_9 = _tmp_8;
x_10 = _tmp_9;
}
goto _start;
}
}
}
else
{
size_t x_79; size_t x_80; uint8_t x_81; 
lean_dec(x_68);
x_79 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_80 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_81 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__14(x_24, x_63, x_79, x_80);
lean_dec(x_63);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_box(0);
x_34 = x_82;
goto block_61;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_24);
x_83 = lean_ctor_get(x_6, 2);
x_84 = lean_nat_add(x_8, x_83);
lean_dec(x_8);
lean_inc(x_2);
{
lean_object* _tmp_6 = x_2;
lean_object* _tmp_7 = x_84;
lean_object* _tmp_8 = lean_box(0);
lean_object* _tmp_9 = lean_box(0);
x_7 = _tmp_6;
x_8 = _tmp_7;
x_9 = _tmp_8;
x_10 = _tmp_9;
}
goto _start;
}
}
}
block_33:
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
x_26 = lean_nat_dec_eq(x_3, x_23);
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_16);
return x_32;
}
block_61:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_34);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_8, x_35);
lean_inc(x_4);
lean_inc(x_1);
x_37 = l_Array_toSubarray___rarg(x_1, x_36, x_4);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 2);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_nat_dec_lt(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_box(0);
x_25 = x_42;
goto block_33;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_40, x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_40);
x_45 = lean_nat_dec_lt(x_39, x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_box(0);
x_25 = x_46;
goto block_33;
}
else
{
size_t x_47; size_t x_48; uint8_t x_49; 
x_47 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_48 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_49 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__9(x_24, x_38, x_47, x_48);
lean_dec(x_38);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_box(0);
x_25 = x_50;
goto block_33;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_24);
x_51 = lean_ctor_get(x_6, 2);
x_52 = lean_nat_add(x_8, x_51);
lean_dec(x_8);
lean_inc(x_2);
{
lean_object* _tmp_6 = x_2;
lean_object* _tmp_7 = x_52;
lean_object* _tmp_8 = lean_box(0);
lean_object* _tmp_9 = lean_box(0);
x_7 = _tmp_6;
x_8 = _tmp_7;
x_9 = _tmp_8;
x_10 = _tmp_9;
}
goto _start;
}
}
}
else
{
size_t x_54; size_t x_55; uint8_t x_56; 
lean_dec(x_43);
x_54 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_55 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_56 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__10(x_24, x_38, x_54, x_55);
lean_dec(x_38);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
x_25 = x_57;
goto block_33;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_24);
x_58 = lean_ctor_get(x_6, 2);
x_59 = lean_nat_add(x_8, x_58);
lean_dec(x_8);
lean_inc(x_2);
{
lean_object* _tmp_6 = x_2;
lean_object* _tmp_7 = x_59;
lean_object* _tmp_8 = lean_box(0);
lean_object* _tmp_9 = lean_box(0);
x_7 = _tmp_6;
x_8 = _tmp_7;
x_9 = _tmp_8;
x_10 = _tmp_9;
}
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_nat_dec_lt(x_7, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
x_19 = lean_nat_sub(x_2, x_7);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_unsigned_to_nat(1u);
lean_inc(x_19);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_21);
lean_inc_n(x_4, 2);
lean_inc(x_1);
x_23 = l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15(x_1, x_4, x_7, x_19, x_22, x_22, x_4, x_20, lean_box(0), lean_box(0), x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_5, 2);
x_28 = lean_nat_add(x_7, x_27);
lean_dec(x_7);
lean_inc(x_4);
{
lean_object* _tmp_5 = x_4;
lean_object* _tmp_6 = x_28;
lean_object* _tmp_7 = lean_box(0);
lean_object* _tmp_8 = lean_box(0);
lean_object* _tmp_14 = x_26;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_9 = _tmp_8;
x_15 = _tmp_14;
}
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_23, 0, x_38);
return x_23;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_dec(x_23);
x_40 = lean_ctor_get(x_25, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_41 = x_25;
} else {
 lean_dec_ref(x_25);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15___closed__1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_1, x_10);
x_12 = l_Lean_instInhabitedName;
x_13 = lean_array_get(x_12, x_11, x_10);
lean_dec(x_11);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
static lean_object* _init_l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_unsigned_to_nat(1u);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___closed__1;
lean_inc(x_1);
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16(x_1, x_8, x_11, x_12, x_11, x_12, x_9, lean_box(0), lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_11);
lean_dec(x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___lambda__1(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_1);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__17(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_name_eq(x_7, x_1);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (x_8 == 0)
{
lean_object* x_11; 
x_11 = lean_array_push(x_5, x_7);
x_3 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__18(size_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; size_t x_14; size_t x_15; 
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_6, x_5, x_9);
x_11 = lean_array_get_size(x_8);
lean_inc(x_2);
x_12 = lean_array_mk(x_2);
x_13 = lean_nat_dec_lt(x_9, x_11);
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
if (x_13 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_8);
x_16 = lean_array_uset(x_10, x_5, x_12);
x_5 = x_15;
x_6 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_11, x_11);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_8);
x_19 = lean_array_uset(x_10, x_5, x_12);
x_5 = x_15;
x_6 = x_19;
goto _start;
}
else
{
size_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_22 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__17(x_3, x_8, x_1, x_21, x_12);
lean_dec(x_8);
x_23 = lean_array_uset(x_10, x_5, x_22);
x_5 = x_15;
x_6 = x_23;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__19(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__20(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_6);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_14 = lean_array_uset(x_8, x_3, x_11);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; size_t x_15; size_t x_16; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
x_10 = l_Array_toSubarray___rarg(x_7, x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_nat_dec_lt(x_12, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_get_size(x_11);
x_19 = lean_nat_dec_le(x_13, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_13);
x_20 = lean_nat_dec_lt(x_12, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
x_3 = x_16;
goto _start;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_23 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_24 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__19(x_1, x_11, x_22, x_23);
lean_dec(x_11);
if (x_24 == 0)
{
lean_dec(x_7);
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_26; 
x_26 = lean_array_push(x_5, x_7);
x_3 = x_16;
x_5 = x_26;
goto _start;
}
}
}
else
{
size_t x_28; size_t x_29; uint8_t x_30; 
lean_dec(x_18);
x_28 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_29 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_30 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__20(x_1, x_11, x_28, x_29);
lean_dec(x_11);
if (x_30 == 0)
{
lean_dec(x_7);
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_32; 
x_32 = lean_array_push(x_5, x_7);
x_3 = x_16;
x_5 = x_32;
goto _start;
}
}
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_1);
x_15 = lean_array_push(x_6, x_1);
x_16 = lean_array_size(x_7);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__18(x_2, x_3, x_1, x_16, x_2, x_7);
lean_dec(x_1);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_4);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_18, x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_14);
return x_29;
}
else
{
size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_31 = l_Array_foldlMUnsafe_fold___at_Lean_mergeStructureResolutionOrders___spec__4(x_17, x_2, x_30, x_4);
lean_dec(x_17);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_14);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(lean_object* x_1, uint8_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = l_Array_isEmpty___rarg(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_14);
lean_free_object(x_6);
lean_inc(x_18);
x_20 = l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(x_18, x_7, x_8, x_9, x_10, x_11, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
if (x_2 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_43; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_array_get_size(x_18);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
x_29 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_25);
if (x_28 == 0)
{
lean_dec(x_26);
lean_inc(x_4);
x_43 = x_4;
goto block_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_26, x_26);
if (x_54 == 0)
{
lean_dec(x_26);
lean_inc(x_4);
x_43 = x_4;
goto block_53;
}
else
{
size_t x_55; lean_object* x_56; 
x_55 = lean_usize_of_nat(x_26);
lean_dec(x_26);
lean_inc(x_4);
x_56 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_25, x_18, x_3, x_55, x_4);
x_43 = x_56;
goto block_53;
}
}
block_42:
{
lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = l_Array_eraseReps___at_Lean_mergeStructureResolutionOrders___spec__7(x_30);
lean_dec(x_30);
x_32 = lean_array_size(x_31);
x_33 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(x_1, x_32, x_3, x_31);
lean_inc(x_25);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_29);
x_35 = lean_array_push(x_16, x_34);
x_36 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_37 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_25, x_3, x_5, x_4, x_35, x_17, x_18, x_36, x_7, x_8, x_9, x_10, x_11, x_24);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_6 = x_40;
x_12 = x_39;
goto _start;
}
block_53:
{
size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_array_size(x_43);
x_45 = l_Array_mapMUnsafe_map___at_Lean_mergeStructureResolutionOrders___spec__10(x_44, x_3, x_43);
x_46 = lean_array_get_size(x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_46, x_47);
x_49 = lean_nat_dec_eq(x_46, x_27);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_27, x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_inc(x_48);
x_51 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_46, x_45, x_48, x_48, lean_box(0), lean_box(0));
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_51;
goto block_42;
}
else
{
lean_object* x_52; 
x_52 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_46, x_45, x_27, x_48, lean_box(0), lean_box(0));
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_52;
goto block_42;
}
}
else
{
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_45;
goto block_42;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_dec(x_20);
x_58 = lean_ctor_get(x_21, 1);
lean_inc(x_58);
lean_dec(x_21);
x_59 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_60 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_58, x_3, x_5, x_4, x_16, x_17, x_18, x_59, x_7, x_8, x_9, x_10, x_11, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_6 = x_63;
x_12 = x_62;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_dec(x_20);
x_66 = lean_ctor_get(x_21, 1);
lean_inc(x_66);
lean_dec(x_21);
x_67 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_68 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_66, x_3, x_5, x_4, x_16, x_17, x_18, x_67, x_7, x_8, x_9, x_10, x_11, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_6 = x_71;
x_12 = x_70;
goto _start;
}
}
else
{
lean_object* x_73; 
lean_dec(x_5);
lean_dec(x_4);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_6, 0);
x_75 = lean_ctor_get(x_14, 0);
x_76 = lean_ctor_get(x_14, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_14);
x_77 = l_Array_isEmpty___rarg(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_free_object(x_6);
lean_inc(x_76);
x_78 = l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(x_76, x_7, x_8, x_9, x_10, x_11, x_12);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
if (x_2 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_101; 
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_array_get_size(x_76);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_lt(x_85, x_84);
x_87 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_83);
if (x_86 == 0)
{
lean_dec(x_84);
lean_inc(x_4);
x_101 = x_4;
goto block_111;
}
else
{
uint8_t x_112; 
x_112 = lean_nat_dec_le(x_84, x_84);
if (x_112 == 0)
{
lean_dec(x_84);
lean_inc(x_4);
x_101 = x_4;
goto block_111;
}
else
{
size_t x_113; lean_object* x_114; 
x_113 = lean_usize_of_nat(x_84);
lean_dec(x_84);
lean_inc(x_4);
x_114 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_83, x_76, x_3, x_113, x_4);
x_101 = x_114;
goto block_111;
}
}
block_100:
{
lean_object* x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = l_Array_eraseReps___at_Lean_mergeStructureResolutionOrders___spec__7(x_88);
lean_dec(x_88);
x_90 = lean_array_size(x_89);
x_91 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(x_1, x_90, x_3, x_89);
lean_inc(x_83);
x_92 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_87);
x_93 = lean_array_push(x_74, x_92);
x_94 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_95 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_83, x_3, x_5, x_4, x_93, x_75, x_76, x_94, x_7, x_8, x_9, x_10, x_11, x_82);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_6 = x_98;
x_12 = x_97;
goto _start;
}
block_111:
{
size_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_102 = lean_array_size(x_101);
x_103 = l_Array_mapMUnsafe_map___at_Lean_mergeStructureResolutionOrders___spec__10(x_102, x_3, x_101);
x_104 = lean_array_get_size(x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_sub(x_104, x_105);
x_107 = lean_nat_dec_eq(x_104, x_85);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_85, x_106);
if (x_108 == 0)
{
lean_object* x_109; 
lean_inc(x_106);
x_109 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_104, x_103, x_106, x_106, lean_box(0), lean_box(0));
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_109;
goto block_100;
}
else
{
lean_object* x_110; 
x_110 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_104, x_103, x_85, x_106, lean_box(0), lean_box(0));
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_110;
goto block_100;
}
}
else
{
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_103;
goto block_100;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_78, 1);
lean_inc(x_115);
lean_dec(x_78);
x_116 = lean_ctor_get(x_79, 1);
lean_inc(x_116);
lean_dec(x_79);
x_117 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_118 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_116, x_3, x_5, x_4, x_74, x_75, x_76, x_117, x_7, x_8, x_9, x_10, x_11, x_115);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
x_6 = x_121;
x_12 = x_120;
goto _start;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_123 = lean_ctor_get(x_78, 1);
lean_inc(x_123);
lean_dec(x_78);
x_124 = lean_ctor_get(x_79, 1);
lean_inc(x_124);
lean_dec(x_79);
x_125 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_126 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_124, x_3, x_5, x_4, x_74, x_75, x_76, x_125, x_7, x_8, x_9, x_10, x_11, x_123);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
x_6 = x_129;
x_12 = x_128;
goto _start;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_5);
lean_dec(x_4);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_75);
lean_ctor_set(x_131, 1, x_76);
lean_ctor_set(x_6, 1, x_131);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_6);
lean_ctor_set(x_132, 1, x_12);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_6, 1);
x_134 = lean_ctor_get(x_6, 0);
lean_inc(x_133);
lean_inc(x_134);
lean_dec(x_6);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_137 = x_133;
} else {
 lean_dec_ref(x_133);
 x_137 = lean_box(0);
}
x_138 = l_Array_isEmpty___rarg(x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_137);
lean_inc(x_136);
x_139 = l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(x_136, x_7, x_8, x_9, x_10, x_11, x_12);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
if (x_2 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; lean_object* x_162; 
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
lean_dec(x_140);
x_145 = lean_array_get_size(x_136);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_nat_dec_lt(x_146, x_145);
x_148 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_144);
if (x_147 == 0)
{
lean_dec(x_145);
lean_inc(x_4);
x_162 = x_4;
goto block_172;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_145, x_145);
if (x_173 == 0)
{
lean_dec(x_145);
lean_inc(x_4);
x_162 = x_4;
goto block_172;
}
else
{
size_t x_174; lean_object* x_175; 
x_174 = lean_usize_of_nat(x_145);
lean_dec(x_145);
lean_inc(x_4);
x_175 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_144, x_136, x_3, x_174, x_4);
x_162 = x_175;
goto block_172;
}
}
block_161:
{
lean_object* x_150; size_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_150 = l_Array_eraseReps___at_Lean_mergeStructureResolutionOrders___spec__7(x_149);
lean_dec(x_149);
x_151 = lean_array_size(x_150);
x_152 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(x_1, x_151, x_3, x_150);
lean_inc(x_144);
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_148);
x_154 = lean_array_push(x_134, x_153);
x_155 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_156 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_144, x_3, x_5, x_4, x_154, x_135, x_136, x_155, x_7, x_8, x_9, x_10, x_11, x_143);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_6 = x_159;
x_12 = x_158;
goto _start;
}
block_172:
{
size_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_163 = lean_array_size(x_162);
x_164 = l_Array_mapMUnsafe_map___at_Lean_mergeStructureResolutionOrders___spec__10(x_163, x_3, x_162);
x_165 = lean_array_get_size(x_164);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_sub(x_165, x_166);
x_168 = lean_nat_dec_eq(x_165, x_146);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = lean_nat_dec_le(x_146, x_167);
if (x_169 == 0)
{
lean_object* x_170; 
lean_inc(x_167);
x_170 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_165, x_164, x_167, x_167, lean_box(0), lean_box(0));
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_170;
goto block_161;
}
else
{
lean_object* x_171; 
x_171 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_165, x_164, x_146, x_167, lean_box(0), lean_box(0));
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_171;
goto block_161;
}
}
else
{
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_164;
goto block_161;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_176 = lean_ctor_get(x_139, 1);
lean_inc(x_176);
lean_dec(x_139);
x_177 = lean_ctor_get(x_140, 1);
lean_inc(x_177);
lean_dec(x_140);
x_178 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_179 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_177, x_3, x_5, x_4, x_134, x_135, x_136, x_178, x_7, x_8, x_9, x_10, x_11, x_176);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_dec(x_180);
x_6 = x_182;
x_12 = x_181;
goto _start;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_139, 1);
lean_inc(x_184);
lean_dec(x_139);
x_185 = lean_ctor_get(x_140, 1);
lean_inc(x_185);
lean_dec(x_140);
x_186 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_187 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_185, x_3, x_5, x_4, x_134, x_135, x_136, x_186, x_7, x_8, x_9, x_10, x_11, x_184);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
lean_dec(x_188);
x_6 = x_190;
x_12 = x_189;
goto _start;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_137)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_137;
}
lean_ctor_set(x_192, 0, x_135);
lean_ctor_set(x_192, 1, x_136);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_134);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_12);
return x_194;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24(lean_object* x_1, uint8_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = l_Array_isEmpty___rarg(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_14);
lean_free_object(x_6);
lean_inc(x_18);
x_20 = l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(x_18, x_7, x_8, x_9, x_10, x_11, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
if (x_2 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_43; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_array_get_size(x_18);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
x_29 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_25);
if (x_28 == 0)
{
lean_dec(x_26);
lean_inc(x_4);
x_43 = x_4;
goto block_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_26, x_26);
if (x_54 == 0)
{
lean_dec(x_26);
lean_inc(x_4);
x_43 = x_4;
goto block_53;
}
else
{
size_t x_55; lean_object* x_56; 
x_55 = lean_usize_of_nat(x_26);
lean_dec(x_26);
lean_inc(x_4);
x_56 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_25, x_18, x_3, x_55, x_4);
x_43 = x_56;
goto block_53;
}
}
block_42:
{
lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = l_Array_eraseReps___at_Lean_mergeStructureResolutionOrders___spec__7(x_30);
lean_dec(x_30);
x_32 = lean_array_size(x_31);
x_33 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(x_1, x_32, x_3, x_31);
lean_inc(x_25);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_29);
x_35 = lean_array_push(x_16, x_34);
x_36 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_37 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_25, x_3, x_5, x_4, x_35, x_17, x_18, x_36, x_7, x_8, x_9, x_10, x_11, x_24);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_6 = x_40;
x_12 = x_39;
goto _start;
}
block_53:
{
size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_array_size(x_43);
x_45 = l_Array_mapMUnsafe_map___at_Lean_mergeStructureResolutionOrders___spec__10(x_44, x_3, x_43);
x_46 = lean_array_get_size(x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_46, x_47);
x_49 = lean_nat_dec_eq(x_46, x_27);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_27, x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_inc(x_48);
x_51 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_46, x_45, x_48, x_48, lean_box(0), lean_box(0));
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_51;
goto block_42;
}
else
{
lean_object* x_52; 
x_52 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_46, x_45, x_27, x_48, lean_box(0), lean_box(0));
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_52;
goto block_42;
}
}
else
{
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_45;
goto block_42;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_dec(x_20);
x_58 = lean_ctor_get(x_21, 1);
lean_inc(x_58);
lean_dec(x_21);
x_59 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_60 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_58, x_3, x_5, x_4, x_16, x_17, x_18, x_59, x_7, x_8, x_9, x_10, x_11, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_6 = x_63;
x_12 = x_62;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_dec(x_20);
x_66 = lean_ctor_get(x_21, 1);
lean_inc(x_66);
lean_dec(x_21);
x_67 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_68 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_66, x_3, x_5, x_4, x_16, x_17, x_18, x_67, x_7, x_8, x_9, x_10, x_11, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_6 = x_71;
x_12 = x_70;
goto _start;
}
}
else
{
lean_object* x_73; 
lean_dec(x_5);
lean_dec(x_4);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_6, 0);
x_75 = lean_ctor_get(x_14, 0);
x_76 = lean_ctor_get(x_14, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_14);
x_77 = l_Array_isEmpty___rarg(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_free_object(x_6);
lean_inc(x_76);
x_78 = l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(x_76, x_7, x_8, x_9, x_10, x_11, x_12);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
if (x_2 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_101; 
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_array_get_size(x_76);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_lt(x_85, x_84);
x_87 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_83);
if (x_86 == 0)
{
lean_dec(x_84);
lean_inc(x_4);
x_101 = x_4;
goto block_111;
}
else
{
uint8_t x_112; 
x_112 = lean_nat_dec_le(x_84, x_84);
if (x_112 == 0)
{
lean_dec(x_84);
lean_inc(x_4);
x_101 = x_4;
goto block_111;
}
else
{
size_t x_113; lean_object* x_114; 
x_113 = lean_usize_of_nat(x_84);
lean_dec(x_84);
lean_inc(x_4);
x_114 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_83, x_76, x_3, x_113, x_4);
x_101 = x_114;
goto block_111;
}
}
block_100:
{
lean_object* x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = l_Array_eraseReps___at_Lean_mergeStructureResolutionOrders___spec__7(x_88);
lean_dec(x_88);
x_90 = lean_array_size(x_89);
x_91 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(x_1, x_90, x_3, x_89);
lean_inc(x_83);
x_92 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_87);
x_93 = lean_array_push(x_74, x_92);
x_94 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_95 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_83, x_3, x_5, x_4, x_93, x_75, x_76, x_94, x_7, x_8, x_9, x_10, x_11, x_82);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_6 = x_98;
x_12 = x_97;
goto _start;
}
block_111:
{
size_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_102 = lean_array_size(x_101);
x_103 = l_Array_mapMUnsafe_map___at_Lean_mergeStructureResolutionOrders___spec__10(x_102, x_3, x_101);
x_104 = lean_array_get_size(x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_sub(x_104, x_105);
x_107 = lean_nat_dec_eq(x_104, x_85);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_85, x_106);
if (x_108 == 0)
{
lean_object* x_109; 
lean_inc(x_106);
x_109 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_104, x_103, x_106, x_106, lean_box(0), lean_box(0));
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_109;
goto block_100;
}
else
{
lean_object* x_110; 
x_110 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_104, x_103, x_85, x_106, lean_box(0), lean_box(0));
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_110;
goto block_100;
}
}
else
{
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_103;
goto block_100;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_78, 1);
lean_inc(x_115);
lean_dec(x_78);
x_116 = lean_ctor_get(x_79, 1);
lean_inc(x_116);
lean_dec(x_79);
x_117 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_118 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_116, x_3, x_5, x_4, x_74, x_75, x_76, x_117, x_7, x_8, x_9, x_10, x_11, x_115);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
x_6 = x_121;
x_12 = x_120;
goto _start;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_123 = lean_ctor_get(x_78, 1);
lean_inc(x_123);
lean_dec(x_78);
x_124 = lean_ctor_get(x_79, 1);
lean_inc(x_124);
lean_dec(x_79);
x_125 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_126 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_124, x_3, x_5, x_4, x_74, x_75, x_76, x_125, x_7, x_8, x_9, x_10, x_11, x_123);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
x_6 = x_129;
x_12 = x_128;
goto _start;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_5);
lean_dec(x_4);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_75);
lean_ctor_set(x_131, 1, x_76);
lean_ctor_set(x_6, 1, x_131);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_6);
lean_ctor_set(x_132, 1, x_12);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_6, 1);
x_134 = lean_ctor_get(x_6, 0);
lean_inc(x_133);
lean_inc(x_134);
lean_dec(x_6);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_137 = x_133;
} else {
 lean_dec_ref(x_133);
 x_137 = lean_box(0);
}
x_138 = l_Array_isEmpty___rarg(x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_137);
lean_inc(x_136);
x_139 = l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(x_136, x_7, x_8, x_9, x_10, x_11, x_12);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
if (x_2 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; lean_object* x_162; 
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
lean_dec(x_140);
x_145 = lean_array_get_size(x_136);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_nat_dec_lt(x_146, x_145);
x_148 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_144);
if (x_147 == 0)
{
lean_dec(x_145);
lean_inc(x_4);
x_162 = x_4;
goto block_172;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_145, x_145);
if (x_173 == 0)
{
lean_dec(x_145);
lean_inc(x_4);
x_162 = x_4;
goto block_172;
}
else
{
size_t x_174; lean_object* x_175; 
x_174 = lean_usize_of_nat(x_145);
lean_dec(x_145);
lean_inc(x_4);
x_175 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_144, x_136, x_3, x_174, x_4);
x_162 = x_175;
goto block_172;
}
}
block_161:
{
lean_object* x_150; size_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_150 = l_Array_eraseReps___at_Lean_mergeStructureResolutionOrders___spec__7(x_149);
lean_dec(x_149);
x_151 = lean_array_size(x_150);
x_152 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(x_1, x_151, x_3, x_150);
lean_inc(x_144);
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_148);
x_154 = lean_array_push(x_134, x_153);
x_155 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_156 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_144, x_3, x_5, x_4, x_154, x_135, x_136, x_155, x_7, x_8, x_9, x_10, x_11, x_143);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_6 = x_159;
x_12 = x_158;
goto _start;
}
block_172:
{
size_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_163 = lean_array_size(x_162);
x_164 = l_Array_mapMUnsafe_map___at_Lean_mergeStructureResolutionOrders___spec__10(x_163, x_3, x_162);
x_165 = lean_array_get_size(x_164);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_sub(x_165, x_166);
x_168 = lean_nat_dec_eq(x_165, x_146);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = lean_nat_dec_le(x_146, x_167);
if (x_169 == 0)
{
lean_object* x_170; 
lean_inc(x_167);
x_170 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_165, x_164, x_167, x_167, lean_box(0), lean_box(0));
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_170;
goto block_161;
}
else
{
lean_object* x_171; 
x_171 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_165, x_164, x_146, x_167, lean_box(0), lean_box(0));
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_171;
goto block_161;
}
}
else
{
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_164;
goto block_161;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_176 = lean_ctor_get(x_139, 1);
lean_inc(x_176);
lean_dec(x_139);
x_177 = lean_ctor_get(x_140, 1);
lean_inc(x_177);
lean_dec(x_140);
x_178 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_179 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_177, x_3, x_5, x_4, x_134, x_135, x_136, x_178, x_7, x_8, x_9, x_10, x_11, x_176);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_dec(x_180);
x_6 = x_182;
x_12 = x_181;
goto _start;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_139, 1);
lean_inc(x_184);
lean_dec(x_139);
x_185 = lean_ctor_get(x_140, 1);
lean_inc(x_185);
lean_dec(x_140);
x_186 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_187 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_185, x_3, x_5, x_4, x_134, x_135, x_136, x_186, x_7, x_8, x_9, x_10, x_11, x_184);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
lean_dec(x_188);
x_6 = x_190;
x_12 = x_189;
goto _start;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_137)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_137;
}
lean_ctor_set(x_192, 0, x_135);
lean_ctor_set(x_192, 1, x_136);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_134);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_12);
return x_194;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(lean_object* x_1, uint8_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = l_Array_isEmpty___rarg(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_14);
lean_free_object(x_6);
lean_inc(x_18);
x_20 = l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(x_18, x_7, x_8, x_9, x_10, x_11, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
if (x_2 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_43; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_array_get_size(x_18);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
x_29 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_25);
if (x_28 == 0)
{
lean_dec(x_26);
lean_inc(x_4);
x_43 = x_4;
goto block_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_26, x_26);
if (x_54 == 0)
{
lean_dec(x_26);
lean_inc(x_4);
x_43 = x_4;
goto block_53;
}
else
{
size_t x_55; lean_object* x_56; 
x_55 = lean_usize_of_nat(x_26);
lean_dec(x_26);
lean_inc(x_4);
x_56 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_25, x_18, x_3, x_55, x_4);
x_43 = x_56;
goto block_53;
}
}
block_42:
{
lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = l_Array_eraseReps___at_Lean_mergeStructureResolutionOrders___spec__7(x_30);
lean_dec(x_30);
x_32 = lean_array_size(x_31);
x_33 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(x_1, x_32, x_3, x_31);
lean_inc(x_25);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_29);
x_35 = lean_array_push(x_16, x_34);
x_36 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_37 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_25, x_3, x_5, x_4, x_35, x_17, x_18, x_36, x_7, x_8, x_9, x_10, x_11, x_24);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_6 = x_40;
x_12 = x_39;
goto _start;
}
block_53:
{
size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_array_size(x_43);
x_45 = l_Array_mapMUnsafe_map___at_Lean_mergeStructureResolutionOrders___spec__10(x_44, x_3, x_43);
x_46 = lean_array_get_size(x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_46, x_47);
x_49 = lean_nat_dec_eq(x_46, x_27);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_27, x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_inc(x_48);
x_51 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_46, x_45, x_48, x_48, lean_box(0), lean_box(0));
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_51;
goto block_42;
}
else
{
lean_object* x_52; 
x_52 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_46, x_45, x_27, x_48, lean_box(0), lean_box(0));
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_52;
goto block_42;
}
}
else
{
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_45;
goto block_42;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_dec(x_20);
x_58 = lean_ctor_get(x_21, 1);
lean_inc(x_58);
lean_dec(x_21);
x_59 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_60 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_58, x_3, x_5, x_4, x_16, x_17, x_18, x_59, x_7, x_8, x_9, x_10, x_11, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_6 = x_63;
x_12 = x_62;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_dec(x_20);
x_66 = lean_ctor_get(x_21, 1);
lean_inc(x_66);
lean_dec(x_21);
x_67 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_68 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_66, x_3, x_5, x_4, x_16, x_17, x_18, x_67, x_7, x_8, x_9, x_10, x_11, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_6 = x_71;
x_12 = x_70;
goto _start;
}
}
else
{
lean_object* x_73; 
lean_dec(x_5);
lean_dec(x_4);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_6, 0);
x_75 = lean_ctor_get(x_14, 0);
x_76 = lean_ctor_get(x_14, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_14);
x_77 = l_Array_isEmpty___rarg(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_free_object(x_6);
lean_inc(x_76);
x_78 = l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(x_76, x_7, x_8, x_9, x_10, x_11, x_12);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
if (x_2 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_101; 
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_array_get_size(x_76);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_lt(x_85, x_84);
x_87 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_83);
if (x_86 == 0)
{
lean_dec(x_84);
lean_inc(x_4);
x_101 = x_4;
goto block_111;
}
else
{
uint8_t x_112; 
x_112 = lean_nat_dec_le(x_84, x_84);
if (x_112 == 0)
{
lean_dec(x_84);
lean_inc(x_4);
x_101 = x_4;
goto block_111;
}
else
{
size_t x_113; lean_object* x_114; 
x_113 = lean_usize_of_nat(x_84);
lean_dec(x_84);
lean_inc(x_4);
x_114 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_83, x_76, x_3, x_113, x_4);
x_101 = x_114;
goto block_111;
}
}
block_100:
{
lean_object* x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = l_Array_eraseReps___at_Lean_mergeStructureResolutionOrders___spec__7(x_88);
lean_dec(x_88);
x_90 = lean_array_size(x_89);
x_91 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(x_1, x_90, x_3, x_89);
lean_inc(x_83);
x_92 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_87);
x_93 = lean_array_push(x_74, x_92);
x_94 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_95 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_83, x_3, x_5, x_4, x_93, x_75, x_76, x_94, x_7, x_8, x_9, x_10, x_11, x_82);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_6 = x_98;
x_12 = x_97;
goto _start;
}
block_111:
{
size_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_102 = lean_array_size(x_101);
x_103 = l_Array_mapMUnsafe_map___at_Lean_mergeStructureResolutionOrders___spec__10(x_102, x_3, x_101);
x_104 = lean_array_get_size(x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_sub(x_104, x_105);
x_107 = lean_nat_dec_eq(x_104, x_85);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_85, x_106);
if (x_108 == 0)
{
lean_object* x_109; 
lean_inc(x_106);
x_109 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_104, x_103, x_106, x_106, lean_box(0), lean_box(0));
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_109;
goto block_100;
}
else
{
lean_object* x_110; 
x_110 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_104, x_103, x_85, x_106, lean_box(0), lean_box(0));
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_110;
goto block_100;
}
}
else
{
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_103;
goto block_100;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_78, 1);
lean_inc(x_115);
lean_dec(x_78);
x_116 = lean_ctor_get(x_79, 1);
lean_inc(x_116);
lean_dec(x_79);
x_117 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_118 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_116, x_3, x_5, x_4, x_74, x_75, x_76, x_117, x_7, x_8, x_9, x_10, x_11, x_115);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
x_6 = x_121;
x_12 = x_120;
goto _start;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_123 = lean_ctor_get(x_78, 1);
lean_inc(x_123);
lean_dec(x_78);
x_124 = lean_ctor_get(x_79, 1);
lean_inc(x_124);
lean_dec(x_79);
x_125 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_126 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_124, x_3, x_5, x_4, x_74, x_75, x_76, x_125, x_7, x_8, x_9, x_10, x_11, x_123);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
x_6 = x_129;
x_12 = x_128;
goto _start;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_5);
lean_dec(x_4);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_75);
lean_ctor_set(x_131, 1, x_76);
lean_ctor_set(x_6, 1, x_131);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_6);
lean_ctor_set(x_132, 1, x_12);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_6, 1);
x_134 = lean_ctor_get(x_6, 0);
lean_inc(x_133);
lean_inc(x_134);
lean_dec(x_6);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_137 = x_133;
} else {
 lean_dec_ref(x_133);
 x_137 = lean_box(0);
}
x_138 = l_Array_isEmpty___rarg(x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_137);
lean_inc(x_136);
x_139 = l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(x_136, x_7, x_8, x_9, x_10, x_11, x_12);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
if (x_2 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; lean_object* x_162; 
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
lean_dec(x_140);
x_145 = lean_array_get_size(x_136);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_nat_dec_lt(x_146, x_145);
x_148 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_144);
if (x_147 == 0)
{
lean_dec(x_145);
lean_inc(x_4);
x_162 = x_4;
goto block_172;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_145, x_145);
if (x_173 == 0)
{
lean_dec(x_145);
lean_inc(x_4);
x_162 = x_4;
goto block_172;
}
else
{
size_t x_174; lean_object* x_175; 
x_174 = lean_usize_of_nat(x_145);
lean_dec(x_145);
lean_inc(x_4);
x_175 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_144, x_136, x_3, x_174, x_4);
x_162 = x_175;
goto block_172;
}
}
block_161:
{
lean_object* x_150; size_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_150 = l_Array_eraseReps___at_Lean_mergeStructureResolutionOrders___spec__7(x_149);
lean_dec(x_149);
x_151 = lean_array_size(x_150);
x_152 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(x_1, x_151, x_3, x_150);
lean_inc(x_144);
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_148);
x_154 = lean_array_push(x_134, x_153);
x_155 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_156 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_144, x_3, x_5, x_4, x_154, x_135, x_136, x_155, x_7, x_8, x_9, x_10, x_11, x_143);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_6 = x_159;
x_12 = x_158;
goto _start;
}
block_172:
{
size_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_163 = lean_array_size(x_162);
x_164 = l_Array_mapMUnsafe_map___at_Lean_mergeStructureResolutionOrders___spec__10(x_163, x_3, x_162);
x_165 = lean_array_get_size(x_164);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_sub(x_165, x_166);
x_168 = lean_nat_dec_eq(x_165, x_146);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = lean_nat_dec_le(x_146, x_167);
if (x_169 == 0)
{
lean_object* x_170; 
lean_inc(x_167);
x_170 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_165, x_164, x_167, x_167, lean_box(0), lean_box(0));
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_170;
goto block_161;
}
else
{
lean_object* x_171; 
x_171 = l_Array_qsort_sort___at_Lean_mergeStructureResolutionOrders___spec__11(x_165, x_164, x_146, x_167, lean_box(0), lean_box(0));
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_171;
goto block_161;
}
}
else
{
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_164;
goto block_161;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_176 = lean_ctor_get(x_139, 1);
lean_inc(x_176);
lean_dec(x_139);
x_177 = lean_ctor_get(x_140, 1);
lean_inc(x_177);
lean_dec(x_140);
x_178 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_179 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_177, x_3, x_5, x_4, x_134, x_135, x_136, x_178, x_7, x_8, x_9, x_10, x_11, x_176);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_dec(x_180);
x_6 = x_182;
x_12 = x_181;
goto _start;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_139, 1);
lean_inc(x_184);
lean_dec(x_139);
x_185 = lean_ctor_get(x_140, 1);
lean_inc(x_185);
lean_dec(x_140);
x_186 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_187 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_185, x_3, x_5, x_4, x_134, x_135, x_136, x_186, x_7, x_8, x_9, x_10, x_11, x_184);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
lean_dec(x_188);
x_6 = x_190;
x_12 = x_189;
goto _start;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_137)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_137;
}
lean_ctor_set(x_192, 0, x_135);
lean_ctor_set(x_192, 1, x_136);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_134);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_12);
return x_194;
}
}
}
}
static lean_object* _init_l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_size(x_2);
x_11 = 0;
lean_inc(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5(x_10, x_11, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_array_get_size(x_14);
lean_inc(x_2);
x_17 = lean_array_push(x_14, x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_insertIdx_loop___rarg(x_18, x_17, x_16);
x_20 = lean_array_get_size(x_19);
x_21 = lean_box(0);
x_22 = lean_nat_dec_lt(x_18, x_20);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_1);
x_23 = lean_array_mk(x_12);
if (x_22 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_20);
lean_dec(x_19);
x_24 = l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(x_2, x_3, x_11, x_24, x_21, x_26, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_2);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_29, 1);
lean_dec(x_34);
lean_ctor_set(x_29, 1, x_32);
lean_ctor_set(x_27, 0, x_29);
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_27, 0, x_36);
return x_27;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_40 = x_29;
} else {
 lean_dec_ref(x_29);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_20, x_20);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_20);
lean_dec(x_19);
x_44 = l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24(x_2, x_3, x_11, x_44, x_21, x_46, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_2);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_47, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
lean_dec(x_48);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_49, 1);
lean_dec(x_54);
lean_ctor_set(x_49, 1, x_52);
lean_ctor_set(x_47, 0, x_49);
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_47, 0, x_56);
return x_47;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_dec(x_47);
x_58 = lean_ctor_get(x_48, 0);
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_ctor_get(x_49, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_60 = x_49;
} else {
 lean_dec_ref(x_49);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
else
{
size_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_63 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_64 = l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1;
x_65 = l_Array_foldlMUnsafe_fold___at_Lean_mergeStructureResolutionOrders___spec__4(x_19, x_11, x_63, x_64);
lean_dec(x_19);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_23);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(x_2, x_3, x_11, x_64, x_21, x_67, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_2);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_68, 0);
lean_dec(x_72);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
lean_dec(x_69);
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_70, 1);
lean_dec(x_75);
lean_ctor_set(x_70, 1, x_73);
lean_ctor_set(x_68, 0, x_70);
return x_68;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_68, 0, x_77);
return x_68;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
lean_dec(x_68);
x_79 = lean_ctor_get(x_69, 0);
lean_inc(x_79);
lean_dec(x_69);
x_80 = lean_ctor_get(x_70, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_81 = x_70;
} else {
 lean_dec_ref(x_70);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_78);
return x_83;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_84 = lean_ctor_get(x_12, 0);
x_85 = lean_ctor_get(x_12, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_12);
x_86 = lean_array_get_size(x_84);
lean_inc(x_2);
x_87 = lean_array_push(x_84, x_2);
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_Array_insertIdx_loop___rarg(x_88, x_87, x_86);
x_90 = lean_array_get_size(x_89);
x_91 = lean_box(0);
x_92 = lean_nat_dec_lt(x_88, x_90);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_mk(x_93);
if (x_92 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_90);
lean_dec(x_89);
x_95 = l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1;
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(x_2, x_3, x_11, x_95, x_91, x_97, x_4, x_5, x_6, x_7, x_8, x_85);
lean_dec(x_2);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_102 = x_98;
} else {
 lean_dec_ref(x_98);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
lean_dec(x_99);
x_104 = lean_ctor_get(x_100, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_105 = x_100;
} else {
 lean_dec_ref(x_100);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_103);
if (lean_is_scalar(x_102)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_102;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_101);
return x_107;
}
else
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_90, x_90);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_90);
lean_dec(x_89);
x_109 = l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1;
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_94);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24(x_2, x_3, x_11, x_109, x_91, x_111, x_4, x_5, x_6, x_7, x_8, x_85);
lean_dec(x_2);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_116 = x_112;
} else {
 lean_dec_ref(x_112);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
lean_dec(x_113);
x_118 = lean_ctor_get(x_114, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_119 = x_114;
} else {
 lean_dec_ref(x_114);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_117);
if (lean_is_scalar(x_116)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_116;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_115);
return x_121;
}
else
{
size_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_122 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_123 = l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1;
x_124 = l_Array_foldlMUnsafe_fold___at_Lean_mergeStructureResolutionOrders___spec__4(x_89, x_11, x_122, x_123);
lean_dec(x_89);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_94);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(x_2, x_3, x_11, x_123, x_91, x_126, x_4, x_5, x_6, x_7, x_8, x_85);
lean_dec(x_2);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_131 = x_127;
} else {
 lean_dec_ref(x_127);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_ctor_get(x_129, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_132);
if (lean_is_scalar(x_131)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_131;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_130);
return x_136;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_insert___at___private_Lean_Structure_0__Lean_setStructureResolutionOrder___spec__1(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_structureResolutionExt;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__3;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 4);
lean_dec(x_14);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___lambda__1), 3, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
x_16 = l_Lean_structureResolutionExt;
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
x_18 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__1;
x_19 = l_Lean_EnvExtension_modifyState___rarg(x_18, x_13, x_15, x_17);
x_20 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__4;
lean_ctor_set(x_10, 4, x_20);
lean_ctor_set(x_10, 0, x_19);
x_21 = lean_st_ref_set(x_7, x_10, x_11);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_take(x_5, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 1);
lean_dec(x_27);
x_28 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__5;
lean_ctor_set(x_24, 1, x_28);
x_29 = lean_st_ref_set(x_5, x_24, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 2);
x_38 = lean_ctor_get(x_24, 3);
x_39 = lean_ctor_get(x_24, 4);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_40 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__5;
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_37);
lean_ctor_set(x_41, 3, x_38);
lean_ctor_set(x_41, 4, x_39);
x_42 = lean_st_ref_set(x_5, x_41, x_25);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_47 = lean_ctor_get(x_10, 0);
x_48 = lean_ctor_get(x_10, 1);
x_49 = lean_ctor_get(x_10, 2);
x_50 = lean_ctor_get(x_10, 3);
x_51 = lean_ctor_get(x_10, 5);
x_52 = lean_ctor_get(x_10, 6);
x_53 = lean_ctor_get(x_10, 7);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_10);
x_54 = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___lambda__1), 3, 2);
lean_closure_set(x_54, 0, x_1);
lean_closure_set(x_54, 1, x_2);
x_55 = l_Lean_structureResolutionExt;
x_56 = lean_ctor_get_uint8(x_55, sizeof(void*)*3);
x_57 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__1;
x_58 = l_Lean_EnvExtension_modifyState___rarg(x_57, x_47, x_54, x_56);
x_59 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__4;
x_60 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_48);
lean_ctor_set(x_60, 2, x_49);
lean_ctor_set(x_60, 3, x_50);
lean_ctor_set(x_60, 4, x_59);
lean_ctor_set(x_60, 5, x_51);
lean_ctor_set(x_60, 6, x_52);
lean_ctor_set(x_60, 7, x_53);
x_61 = lean_st_ref_set(x_7, x_60, x_11);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_take(x_5, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 4);
lean_inc(x_69);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 lean_ctor_release(x_64, 4);
 x_70 = x_64;
} else {
 lean_dec_ref(x_64);
 x_70 = lean_box(0);
}
x_71 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__5;
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 5, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_67);
lean_ctor_set(x_72, 3, x_68);
lean_ctor_set(x_72, 4, x_69);
x_73 = lean_st_ref_set(x_5, x_72, x_65);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
x_76 = lean_box(0);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_2);
x_11 = l_Lean_getStructureParentInfo(x_1, x_2);
x_12 = lean_array_size(x_11);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__1(x_12, x_13, x_11);
lean_inc(x_2);
x_15 = l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4(x_2, x_14, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26(x_2, x_18, x_5, x_6, x_7, x_8, x_9, x_17);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_16);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_13);
x_14 = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_9);
x_15 = lean_box(0);
x_16 = l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3___lambda__1(x_13, x_1, x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_1);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_22);
x_23 = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(x_22, x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3___lambda__1(x_22, x_1, x_2, x_24, x_3, x_4, x_5, x_6, x_7, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_1);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_8 = 1;
x_9 = l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_8 = l_Lean_getStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Array_erase___at_Lean_getAllParentStructures___spec__1(x_10, x_1);
lean_dec(x_1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = l_Array_erase___at_Lean_getAllParentStructures___spec__1(x_12, x_1);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
lean_dec(x_6);
x_15 = lean_array_uget(x_3, x_5);
x_16 = lean_st_ref_take(x_7, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_push(x_17, x_15);
x_20 = lean_st_ref_set(x_7, x_19, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_24 = lean_box(0);
x_5 = x_23;
x_6 = x_24;
x_12 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Server_Completion_unfoldeDefinitionGuarded_x3f(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_Server_Completion_getDotCompletionTypeNames_visit(x_18, x_3, x_4, x_5, x_6, x_7, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_2, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_9);
x_13 = lean_array_push(x_11, x_9);
x_14 = lean_st_ref_set(x_2, x_13, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_6, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
x_20 = l_Lean_isStructure(x_19, x_9);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = l_Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(x_1, x_21, x_2, x_3, x_4, x_5, x_6, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = l_Lean_getAllParentStructures___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_18);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = lean_array_size(x_24);
x_28 = 0;
x_29 = lean_box(0);
x_30 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__27(x_24, x_26, x_24, x_27, x_28, x_29, x_2, x_3, x_4, x_5, x_6, x_25);
lean_dec(x_24);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__9(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__10(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__11(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__13(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__14(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__17(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__18(x_7, x_2, x_3, x_8, x_9, x_6);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__19(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__20(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___lambda__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Lean_Loop_forIn_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3___lambda__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_computeStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getAllParentStructures___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__27(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_Completion_getDotCompletionTypeNames_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Server_Completion_getDotCompletionTypeNames_visit(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_9, x_12);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* initialize_Init_Prelude(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_CompletionUtils(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15___closed__1 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15___closed__1);
l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___closed__1 = _init_l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___closed__1();
lean_mark_persistent(l_Lean_mergeStructureResolutionOrders_selectParent___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___closed__1);
l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1 = _init_l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1();
lean_mark_persistent(l_Lean_mergeStructureResolutionOrders___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___closed__1);
l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__1 = _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__1();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__1);
l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__2 = _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__2();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__2);
l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__3 = _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__3();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__3);
l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__4 = _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__4();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__4);
l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__5 = _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__5();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at_Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
