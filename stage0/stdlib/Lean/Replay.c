// Lean compiler output
// Module: Lean.Replay
// Imports: Lean.CoreM Lean.AddDecl Lean.Util.FoldConsts
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
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__15;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstant___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__3;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstant(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__12;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__7;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Environment_replay___spec__1(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_2777_(lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__3;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__14;
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__6;
lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
static lean_object* l_Lean_Environment_Replay_throwKernelException___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_replayConstant___closed__2;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_instInhabitedPUnit;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_replay___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__5;
LEAN_EXPORT lean_object* l_Lean_Environment_replay(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstant___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__1;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__3;
static lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__1;
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__13;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5(uint64_t, uint64_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___lambda__1(lean_object*);
static lean_object* l_Lean_Environment_Replay_replayConstant___closed__4;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_replay___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__9;
lean_object* l_Lean_throwKernelException___at_Lean_addDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__18;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__1;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Environment_find_x3f___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
static lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_replayConstants___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__17;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__4;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__4;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Environment_replay___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__16;
extern lean_object* l_Lean_instInhabitedConstantInfo;
static uint8_t l_Lean_Environment_Replay_throwKernelException___closed__19;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_replay___spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__2;
uint8_t l_Lean_RBNode_isBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__8;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstants(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__2;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__2;
uint8_t l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3174_(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_replayConstant___closed__3;
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__11;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Environment_Replay_replayConstant___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(uint64_t, uint64_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__10;
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__6(uint64_t, uint64_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = l_Lean_Name_quickCmp(x_1, x_6);
switch (x_9) {
case 0:
{
uint8_t x_10; 
x_10 = l_Lean_RBNode_isBlack___rarg(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(x_1, x_5);
x_12 = 0;
lean_ctor_set(x_2, 0, x_11);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_2);
x_13 = l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(x_1, x_5);
x_14 = l_Lean_RBNode_balLeft___rarg(x_13, x_6, x_7, x_8);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
x_15 = l_Lean_RBNode_appendTrees___rarg(x_5, x_8);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = l_Lean_RBNode_isBlack___rarg(x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(x_1, x_8);
x_18 = 0;
lean_ctor_set(x_2, 3, x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_2);
x_19 = l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(x_1, x_8);
x_20 = l_Lean_RBNode_balRight___rarg(x_5, x_6, x_7, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_25 = l_Lean_Name_quickCmp(x_1, x_22);
switch (x_25) {
case 0:
{
uint8_t x_26; 
x_26 = l_Lean_RBNode_isBlack___rarg(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(x_1, x_21);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(x_1, x_21);
x_31 = l_Lean_RBNode_balLeft___rarg(x_30, x_22, x_23, x_24);
return x_31;
}
}
case 1:
{
lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_22);
x_32 = l_Lean_RBNode_appendTrees___rarg(x_21, x_24);
return x_32;
}
default: 
{
uint8_t x_33; 
x_33 = l_Lean_RBNode_isBlack___rarg(x_24);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(x_1, x_24);
x_35 = 0;
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(x_1, x_24);
x_38 = l_Lean_RBNode_balRight___rarg(x_21, x_22, x_23, x_37);
return x_38;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_NameSet_contains(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_free_object(x_5);
x_13 = lean_st_ref_take(x_3, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 2);
x_19 = lean_box(0);
lean_inc(x_1);
x_20 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_18, x_1, x_19);
x_21 = l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(x_1, x_17);
lean_dec(x_1);
lean_ctor_set(x_14, 2, x_20);
lean_ctor_set(x_14, 1, x_21);
x_22 = lean_st_ref_set(x_3, x_14, x_15);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = 1;
x_26 = lean_box(x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
x_33 = lean_ctor_get(x_14, 2);
x_34 = lean_ctor_get(x_14, 3);
x_35 = lean_ctor_get(x_14, 4);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_36 = lean_box(0);
lean_inc(x_1);
x_37 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_33, x_1, x_36);
x_38 = l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(x_1, x_32);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 4, x_35);
x_40 = lean_st_ref_set(x_3, x_39, x_15);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = 1;
x_44 = lean_box(x_43);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_5);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_NameSet_contains(x_48, x_1);
lean_dec(x_48);
if (x_49 == 0)
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_50 = 0;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_53 = lean_st_ref_take(x_3, x_47);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 4);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 lean_ctor_release(x_54, 4);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
lean_inc(x_1);
x_63 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_58, x_1, x_62);
x_64 = l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(x_1, x_57);
lean_dec(x_1);
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(0, 5, 0);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_59);
lean_ctor_set(x_65, 4, x_60);
x_66 = lean_st_ref_set(x_3, x_65, x_55);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = 1;
x_70 = lean_box(x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_isTodo(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_5, 4);
lean_dec(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_dec(x_10);
x_11 = l_Lean_Environment_Replay_throwKernelException___lambda__1___closed__1;
x_12 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_11);
lean_ctor_set(x_5, 4, x_12);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*12, x_2);
x_13 = l_Lean_throwKernelException___at_Lean_addDecl___spec__1(x_3, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 3);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
x_21 = lean_ctor_get(x_5, 9);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get(x_5, 11);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*12 + 1);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_25 = l_Lean_Environment_Replay_throwKernelException___lambda__1___closed__1;
x_26 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_25);
x_27 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_1);
lean_ctor_set(x_27, 3, x_16);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_27, 5, x_17);
lean_ctor_set(x_27, 6, x_18);
lean_ctor_set(x_27, 7, x_19);
lean_ctor_set(x_27, 8, x_20);
lean_ctor_set(x_27, 9, x_21);
lean_ctor_set(x_27, 10, x_22);
lean_ctor_set(x_27, 11, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*12, x_2);
lean_ctor_set_uint8(x_27, sizeof(void*)*12 + 1, x_24);
x_28 = l_Lean_throwKernelException___at_Lean_addDecl___spec__1(x_3, x_27, x_6, x_7);
return x_28;
}
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal exception #", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_2 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Environment_Replay_throwKernelException___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Environment_Replay_throwKernelException___closed__8;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Environment_Replay_throwKernelException___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__12() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Environment_Replay_throwKernelException___closed__11;
x_3 = l_Lean_Environment_Replay_throwKernelException___closed__10;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Environment_Replay_throwKernelException___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Environment_Replay_throwKernelException___closed__14;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__16() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Environment_Replay_throwKernelException___closed__12;
x_3 = l_Lean_NameSet_empty;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__17() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Environment_Replay_throwKernelException___closed__14;
x_3 = l_Lean_Environment_Replay_throwKernelException___closed__12;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static uint8_t _init_l_Lean_Environment_Replay_throwKernelException___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Environment_Replay_throwKernelException___closed__18;
x_3 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_11; lean_object* x_12; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; 
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = lean_st_ref_get(x_3, x_4);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Environment_Replay_throwKernelException___closed__6;
x_34 = l_Lean_Environment_Replay_throwKernelException___closed__9;
x_35 = l_Lean_Environment_Replay_throwKernelException___closed__12;
x_36 = l_Lean_Environment_Replay_throwKernelException___closed__15;
x_37 = l_Lean_Environment_Replay_throwKernelException___closed__16;
x_38 = l_Lean_Environment_Replay_throwKernelException___closed__17;
x_39 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_35);
lean_ctor_set(x_39, 4, x_36);
lean_ctor_set(x_39, 5, x_37);
lean_ctor_set(x_39, 6, x_38);
x_40 = lean_io_get_num_heartbeats(x_31);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_44 = l_Lean_Environment_Replay_throwKernelException___closed__4;
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_unsigned_to_nat(1000u);
x_47 = lean_box(0);
x_48 = lean_box(0);
x_49 = l_Lean_Environment_Replay_throwKernelException___closed__5;
x_50 = l_Lean_firstFrontendMacroScope;
x_51 = 0;
x_52 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_27);
lean_ctor_set(x_52, 3, x_45);
lean_ctor_set(x_52, 4, x_46);
lean_ctor_set(x_52, 5, x_47);
lean_ctor_set(x_52, 6, x_48);
lean_ctor_set(x_52, 7, x_27);
lean_ctor_set(x_52, 8, x_41);
lean_ctor_set(x_52, 9, x_49);
lean_ctor_set(x_52, 10, x_50);
lean_ctor_set(x_52, 11, x_28);
lean_ctor_set_uint8(x_52, sizeof(void*)*12, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*12 + 1, x_51);
x_53 = lean_st_mk_ref(x_39, x_42);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_st_ref_get(x_54, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Kernel_isDiagnosticsEnabled(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
uint8_t x_97; 
x_97 = l_Lean_Environment_Replay_throwKernelException___closed__19;
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = 1;
x_61 = x_98;
goto block_96;
}
else
{
x_61 = x_51;
goto block_96;
}
}
else
{
uint8_t x_99; 
x_99 = l_Lean_Environment_Replay_throwKernelException___closed__19;
if (x_99 == 0)
{
x_61 = x_51;
goto block_96;
}
else
{
uint8_t x_100; 
x_100 = 1;
x_61 = x_100;
goto block_96;
}
}
block_10:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
block_26:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_MessageData_toString(x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_17);
x_5 = x_14;
goto block_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_5 = x_21;
goto block_10;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
x_5 = x_14;
goto block_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_5 = x_25;
goto block_10;
}
}
}
block_96:
{
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_st_ref_take(x_54, x_58);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 4);
lean_dec(x_67);
x_68 = l_Lean_Environment_Replay_throwKernelException___closed__19;
x_69 = l_Lean_Kernel_enableDiag(x_66, x_68);
lean_ctor_set(x_63, 4, x_36);
lean_ctor_set(x_63, 0, x_69);
x_70 = lean_st_ref_set(x_54, x_63, x_64);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_box(0);
x_73 = l_Lean_Environment_Replay_throwKernelException___lambda__1(x_27, x_68, x_1, x_72, x_52, x_54, x_71);
lean_dec(x_54);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_11 = x_74;
x_12 = x_75;
goto block_26;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_76 = lean_ctor_get(x_63, 0);
x_77 = lean_ctor_get(x_63, 1);
x_78 = lean_ctor_get(x_63, 2);
x_79 = lean_ctor_get(x_63, 3);
x_80 = lean_ctor_get(x_63, 5);
x_81 = lean_ctor_get(x_63, 6);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_63);
x_82 = l_Lean_Environment_Replay_throwKernelException___closed__19;
x_83 = l_Lean_Kernel_enableDiag(x_76, x_82);
x_84 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_77);
lean_ctor_set(x_84, 2, x_78);
lean_ctor_set(x_84, 3, x_79);
lean_ctor_set(x_84, 4, x_36);
lean_ctor_set(x_84, 5, x_80);
lean_ctor_set(x_84, 6, x_81);
x_85 = lean_st_ref_set(x_54, x_84, x_64);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_box(0);
x_88 = l_Lean_Environment_Replay_throwKernelException___lambda__1(x_27, x_82, x_1, x_87, x_52, x_54, x_86);
lean_dec(x_54);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_11 = x_89;
x_12 = x_90;
goto block_26;
}
}
else
{
uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = l_Lean_Environment_Replay_throwKernelException___closed__19;
x_92 = lean_box(0);
x_93 = l_Lean_Environment_Replay_throwKernelException___lambda__1(x_27, x_91, x_1, x_92, x_52, x_54, x_58);
lean_dec(x_54);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_11 = x_94;
x_12 = x_95;
goto block_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Environment_Replay_throwKernelException___lambda__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_throwKernelException(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_box(0);
x_11 = l_Lean_Environment_addDecl(x_8, x_9, x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Environment_Replay_throwKernelException(x_12, x_2, x_3, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_st_ref_take(x_3, x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_14);
x_20 = lean_st_ref_set(x_3, x_16, x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_16, 1);
x_28 = lean_ctor_get(x_16, 2);
x_29 = lean_ctor_get(x_16, 3);
x_30 = lean_ctor_get(x_16, 4);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set(x_31, 4, x_30);
x_32 = lean_st_ref_set(x_3, x_31, x_17);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_addDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_instMonad(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__2;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__3;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__4;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.Data.DHashMap.Internal.AssocList.Basic", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DHashMap.Internal.AssocList.get!", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key is not present in hash table", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__1;
x_2 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(122u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__4;
x_5 = l_panic___rarg(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_2);
if (x_9 == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_7);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(uint64_t x_1, uint64_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_List_reverse___rarg(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_array_get_size(x_14);
x_16 = l_Lean_Name_hash___override(x_12);
x_17 = lean_uint64_shift_right(x_16, x_1);
x_18 = lean_uint64_xor(x_16, x_17);
x_19 = lean_uint64_shift_right(x_18, x_2);
x_20 = lean_uint64_xor(x_18, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = lean_usize_sub(x_22, x_3);
x_24 = lean_usize_land(x_21, x_23);
x_25 = lean_array_uget(x_14, x_24);
x_26 = l_Lean_instInhabitedConstantInfo;
x_27 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2(x_26, x_12, x_25);
lean_dec(x_25);
lean_dec(x_12);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_27);
{
lean_object* _tmp_3 = x_13;
lean_object* _tmp_4 = x_4;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_4);
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_array_get_size(x_31);
x_33 = l_Lean_Name_hash___override(x_29);
x_34 = lean_uint64_shift_right(x_33, x_1);
x_35 = lean_uint64_xor(x_33, x_34);
x_36 = lean_uint64_shift_right(x_35, x_2);
x_37 = lean_uint64_xor(x_35, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_40 = lean_usize_sub(x_39, x_3);
x_41 = lean_usize_land(x_38, x_40);
x_42 = lean_array_uget(x_31, x_41);
x_43 = l_Lean_instInhabitedConstantInfo;
x_44 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2(x_43, x_29, x_42);
lean_dec(x_42);
lean_dec(x_29);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_5);
x_4 = x_30;
x_5 = x_45;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_st_ref_take(x_4, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 2);
x_15 = l_Lean_ConstantInfo_name(x_7);
x_16 = l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(x_15, x_13);
x_17 = l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(x_15, x_14);
lean_dec(x_15);
lean_ctor_set(x_10, 2, x_17);
lean_ctor_set(x_10, 1, x_16);
x_18 = lean_st_ref_set(x_4, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_1 = x_8;
x_2 = x_20;
x_5 = x_19;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_27 = l_Lean_ConstantInfo_name(x_7);
x_28 = l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(x_27, x_23);
x_29 = l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(x_27, x_24);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_26);
x_31 = lean_st_ref_set(x_4, x_30, x_11);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_1 = x_8;
x_2 = x_33;
x_5 = x_32;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5(uint64_t x_1, uint64_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_List_reverse___rarg(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_array_get_size(x_14);
x_16 = l_Lean_Name_hash___override(x_12);
x_17 = lean_uint64_shift_right(x_16, x_1);
x_18 = lean_uint64_xor(x_16, x_17);
x_19 = lean_uint64_shift_right(x_18, x_2);
x_20 = lean_uint64_xor(x_18, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = lean_usize_sub(x_22, x_3);
x_24 = lean_usize_land(x_21, x_23);
x_25 = lean_array_uget(x_14, x_24);
x_26 = l_Lean_instInhabitedConstantInfo;
x_27 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2(x_26, x_12, x_25);
lean_dec(x_25);
lean_dec(x_12);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_27);
{
lean_object* _tmp_3 = x_13;
lean_object* _tmp_4 = x_4;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_4);
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_array_get_size(x_31);
x_33 = l_Lean_Name_hash___override(x_29);
x_34 = lean_uint64_shift_right(x_33, x_1);
x_35 = lean_uint64_xor(x_33, x_34);
x_36 = lean_uint64_shift_right(x_35, x_2);
x_37 = lean_uint64_xor(x_35, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_40 = lean_usize_sub(x_39, x_3);
x_41 = lean_usize_land(x_38, x_40);
x_42 = lean_array_uget(x_31, x_41);
x_43 = l_Lean_instInhabitedConstantInfo;
x_44 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2(x_43, x_29, x_42);
lean_dec(x_42);
lean_dec(x_29);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_5);
x_4 = x_30;
x_5 = x_45;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__6(uint64_t x_1, uint64_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = l_List_reverse___rarg(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = l_Lean_ConstantInfo_inductiveVal_x21(x_13);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_4);
x_17 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5(x_1, x_2, x_3, x_16, x_4, x_7, x_8, x_9);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_ctor_set(x_17, 1, x_19);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_5, 1, x_6);
lean_ctor_set(x_5, 0, x_17);
{
lean_object* _tmp_4 = x_14;
lean_object* _tmp_5 = x_5;
lean_object* _tmp_8 = x_20;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_9 = _tmp_8;
}
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_5, 1, x_6);
lean_ctor_set(x_5, 0, x_24);
{
lean_object* _tmp_4 = x_14;
lean_object* _tmp_5 = x_5;
lean_object* _tmp_8 = x_23;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_9 = _tmp_8;
}
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_28 = l_Lean_ConstantInfo_inductiveVal_x21(x_26);
x_29 = lean_ctor_get(x_28, 4);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_4);
x_30 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5(x_1, x_2, x_3, x_29, x_4, x_7, x_8, x_9);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_6);
x_5 = x_27;
x_6 = x_35;
x_9 = x_32;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_ConstantInfo_getUsedConstantsAsSet(x_7);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Environment_Replay_replayConstants(x_9, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_1 = x_8;
x_2 = x_12;
x_5 = x_11;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__7(x_9, x_10, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_1 = x_8;
x_2 = x_10;
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_ConstantInfo_name(x_5);
x_8 = l_Lean_ConstantInfo_type(x_5);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_9);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l_Lean_ConstantInfo_name(x_11);
x_14 = l_Lean_ConstantInfo_type(x_11);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
x_1 = x_12;
x_2 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_ConstantInfo_name(x_7);
x_10 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__9(x_8, x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_13);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_ConstantInfo_name(x_17);
x_20 = l_Lean_ConstantInfo_type(x_17);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__9(x_18, x_21);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_1 = x_16;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstant___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 2);
x_11 = l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(x_1, x_10);
lean_ctor_set(x_7, 2, x_11);
x_12 = lean_st_ref_set(x_4, x_7, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get(x_7, 2);
x_22 = lean_ctor_get(x_7, 3);
x_23 = lean_ctor_get(x_7, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_24 = l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(x_1, x_21);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
x_26 = lean_st_ref_set(x_4, x_25, x_8);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
static lean_object* _init_l_Lean_Environment_Replay_replayConstant___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Replay", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_replayConstant___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Environment.Replay.replayConstant", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_replayConstant___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_replayConstant___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Environment_Replay_replayConstant___closed__1;
x_2 = l_Lean_Environment_Replay_replayConstant___closed__2;
x_3 = lean_unsigned_to_nat(76u);
x_4 = lean_unsigned_to_nat(50u);
x_5 = l_Lean_Environment_Replay_replayConstant___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_5 = l_Lean_Environment_Replay_isTodo(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
x_17 = l_Lean_Name_hash___override(x_1);
x_18 = 32;
x_19 = lean_uint64_shift_right(x_17, x_18);
x_20 = lean_uint64_xor(x_17, x_19);
x_21 = 16;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_26 = 1;
x_27 = lean_usize_sub(x_25, x_26);
x_28 = lean_usize_land(x_24, x_27);
x_29 = lean_array_uget(x_15, x_28);
lean_dec(x_15);
x_30 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Environment_find_x3f___spec__5(x_1, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = l_Lean_Environment_Replay_replayConstant___closed__4;
x_32 = l_panic___at_Lean_Environment_Replay_replayConstant___spec__1(x_31, x_2, x_3, x_14);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
lean_inc(x_33);
x_34 = l_Lean_ConstantInfo_getUsedConstantsAsSet(x_33);
lean_inc(x_3);
lean_inc(x_2);
x_35 = l_Lean_Environment_Replay_replayConstants(x_34, x_2, x_3, x_14);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_3, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_ctor_get(x_39, 2);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_NameSet_contains(x_41, x_1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_box(0);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
else
{
lean_free_object(x_37);
switch (lean_obj_tag(x_33)) {
case 0:
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_33);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lean_Environment_Replay_addDecl(x_33, x_2, x_3, x_40);
lean_dec(x_33);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_46, x_2, x_3, x_47);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_46);
lean_dec(x_1);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 0);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_45);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_33, 0);
lean_inc(x_53);
lean_dec(x_33);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_Environment_Replay_addDecl(x_54, x_2, x_3, x_40);
lean_dec(x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_56, x_2, x_3, x_57);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_56);
lean_dec(x_1);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_61 = x_55;
} else {
 lean_dec_ref(x_55);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
case 1:
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_33);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_Environment_Replay_addDecl(x_33, x_2, x_3, x_40);
lean_dec(x_33);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_65, x_2, x_3, x_66);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_65);
lean_dec(x_1);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_64);
if (x_68 == 0)
{
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 0);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_64);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_33, 0);
lean_inc(x_72);
lean_dec(x_33);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lean_Environment_Replay_addDecl(x_73, x_2, x_3, x_40);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_75, x_2, x_3, x_76);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_75);
lean_dec(x_1);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_80 = x_74;
} else {
 lean_dec_ref(x_74);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
case 2:
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_33);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = l_Lean_Environment_Replay_addDecl(x_33, x_2, x_3, x_40);
lean_dec(x_33);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_84, x_2, x_3, x_85);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_84);
lean_dec(x_1);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
return x_83;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_83, 0);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_83);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_33, 0);
lean_inc(x_91);
lean_dec(x_33);
x_92 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_Lean_Environment_Replay_addDecl(x_92, x_2, x_3, x_40);
lean_dec(x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_94, x_2, x_3, x_95);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_94);
lean_dec(x_1);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_99 = x_93;
} else {
 lean_dec_ref(x_93);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
case 3:
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_33);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = l_Lean_Environment_Replay_addDecl(x_33, x_2, x_3, x_40);
lean_dec(x_33);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_103, x_2, x_3, x_104);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_103);
lean_dec(x_1);
return x_105;
}
else
{
uint8_t x_106; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_102);
if (x_106 == 0)
{
return x_102;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_102, 0);
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_102);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_33, 0);
lean_inc(x_110);
lean_dec(x_33);
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = l_Lean_Environment_Replay_addDecl(x_111, x_2, x_3, x_40);
lean_dec(x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_113, x_2, x_3, x_114);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_113);
lean_dec(x_1);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = lean_ctor_get(x_112, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_118 = x_112;
} else {
 lean_dec_ref(x_112);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
case 4:
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_33);
x_120 = lean_box(4);
x_121 = l_Lean_Environment_Replay_addDecl(x_120, x_2, x_3, x_40);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_122, x_2, x_3, x_123);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_122);
lean_dec(x_1);
return x_124;
}
else
{
uint8_t x_125; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_121);
if (x_125 == 0)
{
return x_121;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_121, 0);
x_127 = lean_ctor_get(x_121, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_121);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
case 5:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_129 = lean_ctor_get(x_33, 0);
lean_inc(x_129);
lean_dec(x_33);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 3);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_box(0);
x_135 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(x_18, x_21, x_26, x_132, x_134, x_2, x_3, x_40);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_box(0);
x_139 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__4(x_136, x_138, x_2, x_3, x_137);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__6(x_18, x_21, x_26, x_134, x_136, x_134, x_2, x_3, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_142);
x_144 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__8(x_142, x_138, x_2, x_3, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__10(x_142, x_134);
x_147 = 0;
x_148 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_148, 0, x_133);
lean_ctor_set(x_148, 1, x_131);
lean_ctor_set(x_148, 2, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*3, x_147);
x_149 = l_Lean_Environment_Replay_addDecl(x_148, x_2, x_3, x_145);
lean_dec(x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_150, x_2, x_3, x_151);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_150);
lean_dec(x_1);
return x_152;
}
else
{
uint8_t x_153; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_149);
if (x_153 == 0)
{
return x_149;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_149, 0);
x_155 = lean_ctor_get(x_149, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_149);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_142);
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_144);
if (x_157 == 0)
{
return x_144;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_144, 0);
x_159 = lean_ctor_get(x_144, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_144);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
case 6:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_161 = lean_ctor_get(x_33, 0);
lean_inc(x_161);
lean_dec(x_33);
x_162 = lean_st_ref_take(x_3, x_40);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = !lean_is_exclusive(x_163);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_166 = lean_ctor_get(x_163, 3);
x_167 = lean_ctor_get(x_161, 0);
lean_inc(x_167);
lean_dec(x_161);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec(x_167);
x_169 = lean_box(0);
x_170 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_166, x_168, x_169);
lean_ctor_set(x_163, 3, x_170);
x_171 = lean_st_ref_set(x_3, x_163, x_164);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_173 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_169, x_2, x_3, x_172);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_174 = lean_ctor_get(x_163, 0);
x_175 = lean_ctor_get(x_163, 1);
x_176 = lean_ctor_get(x_163, 2);
x_177 = lean_ctor_get(x_163, 3);
x_178 = lean_ctor_get(x_163, 4);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_163);
x_179 = lean_ctor_get(x_161, 0);
lean_inc(x_179);
lean_dec(x_161);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_box(0);
x_182 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_177, x_180, x_181);
x_183 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_183, 0, x_174);
lean_ctor_set(x_183, 1, x_175);
lean_ctor_set(x_183, 2, x_176);
lean_ctor_set(x_183, 3, x_182);
lean_ctor_set(x_183, 4, x_178);
x_184 = lean_st_ref_set(x_3, x_183, x_164);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
x_186 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_181, x_2, x_3, x_185);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_186;
}
}
default: 
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_187 = lean_ctor_get(x_33, 0);
lean_inc(x_187);
lean_dec(x_33);
x_188 = lean_st_ref_take(x_3, x_40);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = !lean_is_exclusive(x_189);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_192 = lean_ctor_get(x_189, 4);
x_193 = lean_ctor_get(x_187, 0);
lean_inc(x_193);
lean_dec(x_187);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec(x_193);
x_195 = lean_box(0);
x_196 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_192, x_194, x_195);
lean_ctor_set(x_189, 4, x_196);
x_197 = lean_st_ref_set(x_3, x_189, x_190);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_195, x_2, x_3, x_198);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_200 = lean_ctor_get(x_189, 0);
x_201 = lean_ctor_get(x_189, 1);
x_202 = lean_ctor_get(x_189, 2);
x_203 = lean_ctor_get(x_189, 3);
x_204 = lean_ctor_get(x_189, 4);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_189);
x_205 = lean_ctor_get(x_187, 0);
lean_inc(x_205);
lean_dec(x_187);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_dec(x_205);
x_207 = lean_box(0);
x_208 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_204, x_206, x_207);
x_209 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_209, 0, x_200);
lean_ctor_set(x_209, 1, x_201);
lean_ctor_set(x_209, 2, x_202);
lean_ctor_set(x_209, 3, x_203);
lean_ctor_set(x_209, 4, x_208);
x_210 = lean_st_ref_set(x_3, x_209, x_190);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_207, x_2, x_3, x_211);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_212;
}
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_213 = lean_ctor_get(x_37, 0);
x_214 = lean_ctor_get(x_37, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_37);
x_215 = lean_ctor_get(x_213, 2);
lean_inc(x_215);
lean_dec(x_213);
x_216 = l_Lean_NameSet_contains(x_215, x_1);
lean_dec(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = lean_box(0);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_214);
return x_218;
}
else
{
switch (lean_obj_tag(x_33)) {
case 0:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = lean_ctor_get(x_33, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_220 = x_33;
} else {
 lean_dec_ref(x_33);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 1, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_219);
x_222 = l_Lean_Environment_Replay_addDecl(x_221, x_2, x_3, x_214);
lean_dec(x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_223, x_2, x_3, x_224);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_223);
lean_dec(x_1);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_226 = lean_ctor_get(x_222, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_222, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_228 = x_222;
} else {
 lean_dec_ref(x_222);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
case 1:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_33, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_231 = x_33;
} else {
 lean_dec_ref(x_33);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 1, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_230);
x_233 = l_Lean_Environment_Replay_addDecl(x_232, x_2, x_3, x_214);
lean_dec(x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_234, x_2, x_3, x_235);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_234);
lean_dec(x_1);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_237 = lean_ctor_get(x_233, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_233, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_239 = x_233;
} else {
 lean_dec_ref(x_233);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
case 2:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_33, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_242 = x_33;
} else {
 lean_dec_ref(x_33);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(2, 1, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_241);
x_244 = l_Lean_Environment_Replay_addDecl(x_243, x_2, x_3, x_214);
lean_dec(x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_245, x_2, x_3, x_246);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_245);
lean_dec(x_1);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_248 = lean_ctor_get(x_244, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_244, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_250 = x_244;
} else {
 lean_dec_ref(x_244);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
case 3:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_33, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_253 = x_33;
} else {
 lean_dec_ref(x_33);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(3, 1, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_252);
x_255 = l_Lean_Environment_Replay_addDecl(x_254, x_2, x_3, x_214);
lean_dec(x_254);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_256, x_2, x_3, x_257);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_256);
lean_dec(x_1);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_259 = lean_ctor_get(x_255, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_255, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_261 = x_255;
} else {
 lean_dec_ref(x_255);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
case 4:
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_33);
x_263 = lean_box(4);
x_264 = l_Lean_Environment_Replay_addDecl(x_263, x_2, x_3, x_214);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_265, x_2, x_3, x_266);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_265);
lean_dec(x_1);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_268 = lean_ctor_get(x_264, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_264, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_270 = x_264;
} else {
 lean_dec_ref(x_264);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
case 5:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_272 = lean_ctor_get(x_33, 0);
lean_inc(x_272);
lean_dec(x_33);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 3);
lean_inc(x_275);
lean_dec(x_272);
x_276 = lean_ctor_get(x_273, 1);
lean_inc(x_276);
lean_dec(x_273);
x_277 = lean_box(0);
x_278 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(x_18, x_21, x_26, x_275, x_277, x_2, x_3, x_214);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_281 = lean_box(0);
x_282 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__4(x_279, x_281, x_2, x_3, x_280);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_284 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__6(x_18, x_21, x_26, x_277, x_279, x_277, x_2, x_3, x_283);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_285);
x_287 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__8(x_285, x_281, x_2, x_3, x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; 
x_288 = lean_ctor_get(x_287, 1);
lean_inc(x_288);
lean_dec(x_287);
x_289 = l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__10(x_285, x_277);
x_290 = 0;
x_291 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_291, 0, x_276);
lean_ctor_set(x_291, 1, x_274);
lean_ctor_set(x_291, 2, x_289);
lean_ctor_set_uint8(x_291, sizeof(void*)*3, x_290);
x_292 = l_Lean_Environment_Replay_addDecl(x_291, x_2, x_3, x_288);
lean_dec(x_291);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_293, x_2, x_3, x_294);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_293);
lean_dec(x_1);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_296 = lean_ctor_get(x_292, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_292, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_298 = x_292;
} else {
 lean_dec_ref(x_292);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_285);
lean_dec(x_276);
lean_dec(x_274);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_300 = lean_ctor_get(x_287, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_287, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_302 = x_287;
} else {
 lean_dec_ref(x_287);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
case 6:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_304 = lean_ctor_get(x_33, 0);
lean_inc(x_304);
lean_dec(x_33);
x_305 = lean_st_ref_take(x_3, x_214);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_308 = lean_ctor_get(x_306, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_306, 1);
lean_inc(x_309);
x_310 = lean_ctor_get(x_306, 2);
lean_inc(x_310);
x_311 = lean_ctor_get(x_306, 3);
lean_inc(x_311);
x_312 = lean_ctor_get(x_306, 4);
lean_inc(x_312);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 lean_ctor_release(x_306, 2);
 lean_ctor_release(x_306, 3);
 lean_ctor_release(x_306, 4);
 x_313 = x_306;
} else {
 lean_dec_ref(x_306);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_304, 0);
lean_inc(x_314);
lean_dec(x_304);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
lean_dec(x_314);
x_316 = lean_box(0);
x_317 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_311, x_315, x_316);
if (lean_is_scalar(x_313)) {
 x_318 = lean_alloc_ctor(0, 5, 0);
} else {
 x_318 = x_313;
}
lean_ctor_set(x_318, 0, x_308);
lean_ctor_set(x_318, 1, x_309);
lean_ctor_set(x_318, 2, x_310);
lean_ctor_set(x_318, 3, x_317);
lean_ctor_set(x_318, 4, x_312);
x_319 = lean_st_ref_set(x_3, x_318, x_307);
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
lean_dec(x_319);
x_321 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_316, x_2, x_3, x_320);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_321;
}
default: 
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_322 = lean_ctor_get(x_33, 0);
lean_inc(x_322);
lean_dec(x_33);
x_323 = lean_st_ref_take(x_3, x_214);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_ctor_get(x_324, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_324, 1);
lean_inc(x_327);
x_328 = lean_ctor_get(x_324, 2);
lean_inc(x_328);
x_329 = lean_ctor_get(x_324, 3);
lean_inc(x_329);
x_330 = lean_ctor_get(x_324, 4);
lean_inc(x_330);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 lean_ctor_release(x_324, 2);
 lean_ctor_release(x_324, 3);
 lean_ctor_release(x_324, 4);
 x_331 = x_324;
} else {
 lean_dec_ref(x_324);
 x_331 = lean_box(0);
}
x_332 = lean_ctor_get(x_322, 0);
lean_inc(x_332);
lean_dec(x_322);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
lean_dec(x_332);
x_334 = lean_box(0);
x_335 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_330, x_333, x_334);
if (lean_is_scalar(x_331)) {
 x_336 = lean_alloc_ctor(0, 5, 0);
} else {
 x_336 = x_331;
}
lean_ctor_set(x_336, 0, x_326);
lean_ctor_set(x_336, 1, x_327);
lean_ctor_set(x_336, 2, x_328);
lean_ctor_set(x_336, 3, x_329);
lean_ctor_set(x_336, 4, x_335);
x_337 = lean_st_ref_set(x_3, x_336, x_325);
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
lean_dec(x_337);
x_339 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_334, x_2, x_3, x_338);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_339;
}
}
}
}
}
else
{
uint8_t x_340; 
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_340 = !lean_is_exclusive(x_35);
if (x_340 == 0)
{
return x_35;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_35, 0);
x_342 = lean_ctor_get(x_35, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_35);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_replayConstants___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_replayConstants___spec__1(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Environment_Replay_replayConstant(x_9, x_3, x_4, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_1 = x_10;
x_2 = x_20;
x_5 = x_19;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstants(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_replayConstants___spec__1(x_1, x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint64_t x_9; uint64_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_10 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(x_9, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint64_t x_9; uint64_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_10 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5(x_9, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint64_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_11 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__6(x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstant___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_array_get_size(x_7);
x_9 = l_Lean_Name_hash___override(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_7, x_20);
lean_dec(x_7);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Environment_find_x3f___spec__5(x_2, x_21);
lean_dec(x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_6, 0);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_array_get_size(x_27);
x_29 = l_Lean_Name_hash___override(x_2);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_27, x_40);
lean_dec(x_27);
x_42 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Environment_find_x3f___spec__5(x_2, x_41);
lean_dec(x_41);
return x_42;
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("No such constructor ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid constructor ", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_st_ref_get(x_4, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_21, x_9);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
x_23 = 1;
x_24 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_25 = l_Lean_Name_toString(x_9, x_23, x_24);
x_26 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_29 = lean_string_append(x_27, x_28);
lean_ctor_set_tag(x_12, 18);
lean_ctor_set(x_12, 0, x_29);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_30; 
lean_free_object(x_12);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
if (lean_obj_tag(x_30) == 6)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_3, 1);
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_array_get_size(x_32);
x_35 = l_Lean_Name_hash___override(x_9);
x_36 = 32;
x_37 = lean_uint64_shift_right(x_35, x_36);
x_38 = lean_uint64_xor(x_35, x_37);
x_39 = 16;
x_40 = lean_uint64_shift_right(x_38, x_39);
x_41 = lean_uint64_xor(x_38, x_40);
x_42 = lean_uint64_to_usize(x_41);
x_43 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_44 = 1;
x_45 = lean_usize_sub(x_43, x_44);
x_46 = lean_usize_land(x_42, x_45);
x_47 = lean_array_uget(x_32, x_46);
x_48 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Environment_find_x3f___spec__5(x_9, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_33);
lean_dec(x_10);
x_49 = 1;
x_50 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_51 = l_Lean_Name_toString(x_9, x_49, x_50);
x_52 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_55 = lean_string_append(x_53, x_54);
lean_ctor_set_tag(x_30, 18);
lean_ctor_set(x_30, 0, x_55);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
else
{
lean_object* x_56; 
lean_free_object(x_30);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
lean_dec(x_48);
if (lean_obj_tag(x_56) == 6)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_2777_(x_33, x_58);
lean_dec(x_58);
lean_dec(x_33);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_10);
x_60 = 1;
x_61 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_62 = l_Lean_Name_toString(x_9, x_60, x_61);
x_63 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__3;
x_64 = lean_string_append(x_63, x_62);
lean_dec(x_62);
x_65 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_66 = lean_string_append(x_64, x_65);
lean_ctor_set_tag(x_56, 18);
lean_ctor_set(x_56, 0, x_66);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_56);
return x_16;
}
else
{
lean_object* x_67; 
lean_free_object(x_56);
lean_free_object(x_16);
lean_dec(x_9);
x_67 = lean_box(0);
x_1 = x_10;
x_2 = x_67;
x_5 = x_19;
goto _start;
}
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_56, 0);
lean_inc(x_69);
lean_dec(x_56);
x_70 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_2777_(x_33, x_69);
lean_dec(x_69);
lean_dec(x_33);
if (x_70 == 0)
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_10);
x_71 = 1;
x_72 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_73 = l_Lean_Name_toString(x_9, x_71, x_72);
x_74 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__3;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_78);
return x_16;
}
else
{
lean_object* x_79; 
lean_free_object(x_16);
lean_dec(x_9);
x_79 = lean_box(0);
x_1 = x_10;
x_2 = x_79;
x_5 = x_19;
goto _start;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_33);
lean_dec(x_10);
x_81 = !lean_is_exclusive(x_56);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_56, 0);
lean_dec(x_82);
x_83 = 1;
x_84 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_85 = l_Lean_Name_toString(x_9, x_83, x_84);
x_86 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_87 = lean_string_append(x_86, x_85);
lean_dec(x_85);
x_88 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_89 = lean_string_append(x_87, x_88);
lean_ctor_set_tag(x_56, 18);
lean_ctor_set(x_56, 0, x_89);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_56);
return x_16;
}
else
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_56);
x_90 = 1;
x_91 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_92 = l_Lean_Name_toString(x_9, x_90, x_91);
x_93 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_94 = lean_string_append(x_93, x_92);
lean_dec(x_92);
x_95 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_96 = lean_string_append(x_94, x_95);
x_97 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_97);
return x_16;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; size_t x_108; size_t x_109; size_t x_110; size_t x_111; size_t x_112; lean_object* x_113; lean_object* x_114; 
x_98 = lean_ctor_get(x_3, 1);
x_99 = lean_ctor_get(x_30, 0);
lean_inc(x_99);
lean_dec(x_30);
x_100 = lean_array_get_size(x_98);
x_101 = l_Lean_Name_hash___override(x_9);
x_102 = 32;
x_103 = lean_uint64_shift_right(x_101, x_102);
x_104 = lean_uint64_xor(x_101, x_103);
x_105 = 16;
x_106 = lean_uint64_shift_right(x_104, x_105);
x_107 = lean_uint64_xor(x_104, x_106);
x_108 = lean_uint64_to_usize(x_107);
x_109 = lean_usize_of_nat(x_100);
lean_dec(x_100);
x_110 = 1;
x_111 = lean_usize_sub(x_109, x_110);
x_112 = lean_usize_land(x_108, x_111);
x_113 = lean_array_uget(x_98, x_112);
x_114 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Environment_find_x3f___spec__5(x_9, x_113);
lean_dec(x_113);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_99);
lean_dec(x_10);
x_115 = 1;
x_116 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_117 = l_Lean_Name_toString(x_9, x_115, x_116);
x_118 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_119 = lean_string_append(x_118, x_117);
lean_dec(x_117);
x_120 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_121 = lean_string_append(x_119, x_120);
x_122 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_122);
return x_16;
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_114, 0);
lean_inc(x_123);
lean_dec(x_114);
if (lean_obj_tag(x_123) == 6)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
x_126 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_2777_(x_99, x_124);
lean_dec(x_124);
lean_dec(x_99);
if (x_126 == 0)
{
uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_10);
x_127 = 1;
x_128 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_129 = l_Lean_Name_toString(x_9, x_127, x_128);
x_130 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__3;
x_131 = lean_string_append(x_130, x_129);
lean_dec(x_129);
x_132 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_133 = lean_string_append(x_131, x_132);
if (lean_is_scalar(x_125)) {
 x_134 = lean_alloc_ctor(18, 1, 0);
} else {
 x_134 = x_125;
 lean_ctor_set_tag(x_134, 18);
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_134);
return x_16;
}
else
{
lean_object* x_135; 
lean_dec(x_125);
lean_free_object(x_16);
lean_dec(x_9);
x_135 = lean_box(0);
x_1 = x_10;
x_2 = x_135;
x_5 = x_19;
goto _start;
}
}
else
{
lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_99);
lean_dec(x_10);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_137 = x_123;
} else {
 lean_dec_ref(x_123);
 x_137 = lean_box(0);
}
x_138 = 1;
x_139 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_140 = l_Lean_Name_toString(x_9, x_138, x_139);
x_141 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_142 = lean_string_append(x_141, x_140);
lean_dec(x_140);
x_143 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_144 = lean_string_append(x_142, x_143);
if (lean_is_scalar(x_137)) {
 x_145 = lean_alloc_ctor(18, 1, 0);
} else {
 x_145 = x_137;
 lean_ctor_set_tag(x_145, 18);
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_145);
return x_16;
}
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_10);
x_146 = !lean_is_exclusive(x_30);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_147 = lean_ctor_get(x_30, 0);
lean_dec(x_147);
x_148 = 1;
x_149 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_150 = l_Lean_Name_toString(x_9, x_148, x_149);
x_151 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_152 = lean_string_append(x_151, x_150);
lean_dec(x_150);
x_153 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_154 = lean_string_append(x_152, x_153);
lean_ctor_set_tag(x_30, 18);
lean_ctor_set(x_30, 0, x_154);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
else
{
uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_30);
x_155 = 1;
x_156 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_157 = l_Lean_Name_toString(x_9, x_155, x_156);
x_158 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_159 = lean_string_append(x_158, x_157);
lean_dec(x_157);
x_160 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_161 = lean_string_append(x_159, x_160);
x_162 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_162);
return x_16;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_ctor_get(x_16, 0);
x_164 = lean_ctor_get(x_16, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_16);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_167 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_166, x_9);
if (lean_obj_tag(x_167) == 0)
{
uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_10);
x_168 = 1;
x_169 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_170 = l_Lean_Name_toString(x_9, x_168, x_169);
x_171 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_172 = lean_string_append(x_171, x_170);
lean_dec(x_170);
x_173 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_174 = lean_string_append(x_172, x_173);
lean_ctor_set_tag(x_12, 18);
lean_ctor_set(x_12, 0, x_174);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_12);
lean_ctor_set(x_175, 1, x_164);
return x_175;
}
else
{
lean_object* x_176; 
lean_free_object(x_12);
x_176 = lean_ctor_get(x_167, 0);
lean_inc(x_176);
lean_dec(x_167);
if (lean_obj_tag(x_176) == 6)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; uint64_t x_187; size_t x_188; size_t x_189; size_t x_190; size_t x_191; size_t x_192; lean_object* x_193; lean_object* x_194; 
x_177 = lean_ctor_get(x_3, 1);
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
x_180 = lean_array_get_size(x_177);
x_181 = l_Lean_Name_hash___override(x_9);
x_182 = 32;
x_183 = lean_uint64_shift_right(x_181, x_182);
x_184 = lean_uint64_xor(x_181, x_183);
x_185 = 16;
x_186 = lean_uint64_shift_right(x_184, x_185);
x_187 = lean_uint64_xor(x_184, x_186);
x_188 = lean_uint64_to_usize(x_187);
x_189 = lean_usize_of_nat(x_180);
lean_dec(x_180);
x_190 = 1;
x_191 = lean_usize_sub(x_189, x_190);
x_192 = lean_usize_land(x_188, x_191);
x_193 = lean_array_uget(x_177, x_192);
x_194 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Environment_find_x3f___spec__5(x_9, x_193);
lean_dec(x_193);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_178);
lean_dec(x_10);
x_195 = 1;
x_196 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_197 = l_Lean_Name_toString(x_9, x_195, x_196);
x_198 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_199 = lean_string_append(x_198, x_197);
lean_dec(x_197);
x_200 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_201 = lean_string_append(x_199, x_200);
if (lean_is_scalar(x_179)) {
 x_202 = lean_alloc_ctor(18, 1, 0);
} else {
 x_202 = x_179;
 lean_ctor_set_tag(x_202, 18);
}
lean_ctor_set(x_202, 0, x_201);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_164);
return x_203;
}
else
{
lean_object* x_204; 
lean_dec(x_179);
x_204 = lean_ctor_get(x_194, 0);
lean_inc(x_204);
lean_dec(x_194);
if (lean_obj_tag(x_204) == 6)
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
x_207 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_2777_(x_178, x_205);
lean_dec(x_205);
lean_dec(x_178);
if (x_207 == 0)
{
uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_10);
x_208 = 1;
x_209 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_210 = l_Lean_Name_toString(x_9, x_208, x_209);
x_211 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__3;
x_212 = lean_string_append(x_211, x_210);
lean_dec(x_210);
x_213 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_214 = lean_string_append(x_212, x_213);
if (lean_is_scalar(x_206)) {
 x_215 = lean_alloc_ctor(18, 1, 0);
} else {
 x_215 = x_206;
 lean_ctor_set_tag(x_215, 18);
}
lean_ctor_set(x_215, 0, x_214);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_164);
return x_216;
}
else
{
lean_object* x_217; 
lean_dec(x_206);
lean_dec(x_9);
x_217 = lean_box(0);
x_1 = x_10;
x_2 = x_217;
x_5 = x_164;
goto _start;
}
}
else
{
lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_178);
lean_dec(x_10);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_219 = x_204;
} else {
 lean_dec_ref(x_204);
 x_219 = lean_box(0);
}
x_220 = 1;
x_221 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_222 = l_Lean_Name_toString(x_9, x_220, x_221);
x_223 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_224 = lean_string_append(x_223, x_222);
lean_dec(x_222);
x_225 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_226 = lean_string_append(x_224, x_225);
if (lean_is_scalar(x_219)) {
 x_227 = lean_alloc_ctor(18, 1, 0);
} else {
 x_227 = x_219;
 lean_ctor_set_tag(x_227, 18);
}
lean_ctor_set(x_227, 0, x_226);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_164);
return x_228;
}
}
}
else
{
lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_10);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_229 = x_176;
} else {
 lean_dec_ref(x_176);
 x_229 = lean_box(0);
}
x_230 = 1;
x_231 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_232 = l_Lean_Name_toString(x_9, x_230, x_231);
x_233 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_234 = lean_string_append(x_233, x_232);
lean_dec(x_232);
x_235 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_236 = lean_string_append(x_234, x_235);
if (lean_is_scalar(x_229)) {
 x_237 = lean_alloc_ctor(18, 1, 0);
} else {
 x_237 = x_229;
 lean_ctor_set_tag(x_237, 18);
}
lean_ctor_set(x_237, 0, x_236);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_164);
return x_238;
}
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_12);
x_239 = lean_ctor_get(x_11, 1);
lean_inc(x_239);
lean_dec(x_11);
x_240 = lean_st_ref_get(x_4, x_239);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_241, 0);
lean_inc(x_244);
lean_dec(x_241);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec(x_244);
x_246 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_245, x_9);
if (lean_obj_tag(x_246) == 0)
{
uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_10);
x_247 = 1;
x_248 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_249 = l_Lean_Name_toString(x_9, x_247, x_248);
x_250 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_251 = lean_string_append(x_250, x_249);
lean_dec(x_249);
x_252 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_253 = lean_string_append(x_251, x_252);
x_254 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_254, 0, x_253);
if (lean_is_scalar(x_243)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_243;
 lean_ctor_set_tag(x_255, 1);
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_242);
return x_255;
}
else
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_246, 0);
lean_inc(x_256);
lean_dec(x_246);
if (lean_obj_tag(x_256) == 6)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint64_t x_261; uint64_t x_262; uint64_t x_263; uint64_t x_264; uint64_t x_265; uint64_t x_266; uint64_t x_267; size_t x_268; size_t x_269; size_t x_270; size_t x_271; size_t x_272; lean_object* x_273; lean_object* x_274; 
x_257 = lean_ctor_get(x_3, 1);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_259 = x_256;
} else {
 lean_dec_ref(x_256);
 x_259 = lean_box(0);
}
x_260 = lean_array_get_size(x_257);
x_261 = l_Lean_Name_hash___override(x_9);
x_262 = 32;
x_263 = lean_uint64_shift_right(x_261, x_262);
x_264 = lean_uint64_xor(x_261, x_263);
x_265 = 16;
x_266 = lean_uint64_shift_right(x_264, x_265);
x_267 = lean_uint64_xor(x_264, x_266);
x_268 = lean_uint64_to_usize(x_267);
x_269 = lean_usize_of_nat(x_260);
lean_dec(x_260);
x_270 = 1;
x_271 = lean_usize_sub(x_269, x_270);
x_272 = lean_usize_land(x_268, x_271);
x_273 = lean_array_uget(x_257, x_272);
x_274 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Environment_find_x3f___spec__5(x_9, x_273);
lean_dec(x_273);
if (lean_obj_tag(x_274) == 0)
{
uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_258);
lean_dec(x_10);
x_275 = 1;
x_276 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_277 = l_Lean_Name_toString(x_9, x_275, x_276);
x_278 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_279 = lean_string_append(x_278, x_277);
lean_dec(x_277);
x_280 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_281 = lean_string_append(x_279, x_280);
if (lean_is_scalar(x_259)) {
 x_282 = lean_alloc_ctor(18, 1, 0);
} else {
 x_282 = x_259;
 lean_ctor_set_tag(x_282, 18);
}
lean_ctor_set(x_282, 0, x_281);
if (lean_is_scalar(x_243)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_243;
 lean_ctor_set_tag(x_283, 1);
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_242);
return x_283;
}
else
{
lean_object* x_284; 
lean_dec(x_259);
x_284 = lean_ctor_get(x_274, 0);
lean_inc(x_284);
lean_dec(x_274);
if (lean_obj_tag(x_284) == 6)
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 x_286 = x_284;
} else {
 lean_dec_ref(x_284);
 x_286 = lean_box(0);
}
x_287 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_2777_(x_258, x_285);
lean_dec(x_285);
lean_dec(x_258);
if (x_287 == 0)
{
uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_10);
x_288 = 1;
x_289 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_290 = l_Lean_Name_toString(x_9, x_288, x_289);
x_291 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__3;
x_292 = lean_string_append(x_291, x_290);
lean_dec(x_290);
x_293 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_294 = lean_string_append(x_292, x_293);
if (lean_is_scalar(x_286)) {
 x_295 = lean_alloc_ctor(18, 1, 0);
} else {
 x_295 = x_286;
 lean_ctor_set_tag(x_295, 18);
}
lean_ctor_set(x_295, 0, x_294);
if (lean_is_scalar(x_243)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_243;
 lean_ctor_set_tag(x_296, 1);
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_242);
return x_296;
}
else
{
lean_object* x_297; 
lean_dec(x_286);
lean_dec(x_243);
lean_dec(x_9);
x_297 = lean_box(0);
x_1 = x_10;
x_2 = x_297;
x_5 = x_242;
goto _start;
}
}
else
{
lean_object* x_299; uint8_t x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_258);
lean_dec(x_10);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 x_299 = x_284;
} else {
 lean_dec_ref(x_284);
 x_299 = lean_box(0);
}
x_300 = 1;
x_301 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_302 = l_Lean_Name_toString(x_9, x_300, x_301);
x_303 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_304 = lean_string_append(x_303, x_302);
lean_dec(x_302);
x_305 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_306 = lean_string_append(x_304, x_305);
if (lean_is_scalar(x_299)) {
 x_307 = lean_alloc_ctor(18, 1, 0);
} else {
 x_307 = x_299;
 lean_ctor_set_tag(x_307, 18);
}
lean_ctor_set(x_307, 0, x_306);
if (lean_is_scalar(x_243)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_243;
 lean_ctor_set_tag(x_308, 1);
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_242);
return x_308;
}
}
}
else
{
lean_object* x_309; uint8_t x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_10);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_309 = x_256;
} else {
 lean_dec_ref(x_256);
 x_309 = lean_box(0);
}
x_310 = 1;
x_311 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_312 = l_Lean_Name_toString(x_9, x_310, x_311);
x_313 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_314 = lean_string_append(x_313, x_312);
lean_dec(x_312);
x_315 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_316 = lean_string_append(x_314, x_315);
if (lean_is_scalar(x_309)) {
 x_317 = lean_alloc_ctor(18, 1, 0);
} else {
 x_317 = x_309;
 lean_ctor_set_tag(x_317, 18);
}
lean_ctor_set(x_317, 0, x_316);
if (lean_is_scalar(x_243)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_243;
 lean_ctor_set_tag(x_318, 1);
}
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_242);
return x_318;
}
}
}
}
else
{
uint8_t x_319; 
lean_dec(x_10);
lean_dec(x_9);
x_319 = !lean_is_exclusive(x_11);
if (x_319 == 0)
{
return x_11;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_11, 0);
x_321 = lean_ctor_get(x_11, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_11);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 3);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2(x_7, x_8, x_1, x_2, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_checkPostponedConstructors(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("No such recursor ", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid recursor ", 17, 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_st_ref_get(x_4, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_21, x_9);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
x_23 = 1;
x_24 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_25 = l_Lean_Name_toString(x_9, x_23, x_24);
x_26 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_29 = lean_string_append(x_27, x_28);
lean_ctor_set_tag(x_12, 18);
lean_ctor_set(x_12, 0, x_29);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_30; 
lean_free_object(x_12);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
if (lean_obj_tag(x_30) == 7)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_3, 1);
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_array_get_size(x_32);
x_35 = l_Lean_Name_hash___override(x_9);
x_36 = 32;
x_37 = lean_uint64_shift_right(x_35, x_36);
x_38 = lean_uint64_xor(x_35, x_37);
x_39 = 16;
x_40 = lean_uint64_shift_right(x_38, x_39);
x_41 = lean_uint64_xor(x_38, x_40);
x_42 = lean_uint64_to_usize(x_41);
x_43 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_44 = 1;
x_45 = lean_usize_sub(x_43, x_44);
x_46 = lean_usize_land(x_42, x_45);
x_47 = lean_array_uget(x_32, x_46);
x_48 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Environment_find_x3f___spec__5(x_9, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_33);
lean_dec(x_10);
x_49 = 1;
x_50 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_51 = l_Lean_Name_toString(x_9, x_49, x_50);
x_52 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_55 = lean_string_append(x_53, x_54);
lean_ctor_set_tag(x_30, 18);
lean_ctor_set(x_30, 0, x_55);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
else
{
lean_object* x_56; 
lean_free_object(x_30);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
lean_dec(x_48);
if (lean_obj_tag(x_56) == 7)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3174_(x_33, x_58);
lean_dec(x_58);
lean_dec(x_33);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_10);
x_60 = 1;
x_61 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_62 = l_Lean_Name_toString(x_9, x_60, x_61);
x_63 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
x_64 = lean_string_append(x_63, x_62);
lean_dec(x_62);
x_65 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_66 = lean_string_append(x_64, x_65);
lean_ctor_set_tag(x_56, 18);
lean_ctor_set(x_56, 0, x_66);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_56);
return x_16;
}
else
{
lean_object* x_67; 
lean_free_object(x_56);
lean_free_object(x_16);
lean_dec(x_9);
x_67 = lean_box(0);
x_1 = x_10;
x_2 = x_67;
x_5 = x_19;
goto _start;
}
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_56, 0);
lean_inc(x_69);
lean_dec(x_56);
x_70 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3174_(x_33, x_69);
lean_dec(x_69);
lean_dec(x_33);
if (x_70 == 0)
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_10);
x_71 = 1;
x_72 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_73 = l_Lean_Name_toString(x_9, x_71, x_72);
x_74 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_78);
return x_16;
}
else
{
lean_object* x_79; 
lean_free_object(x_16);
lean_dec(x_9);
x_79 = lean_box(0);
x_1 = x_10;
x_2 = x_79;
x_5 = x_19;
goto _start;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_33);
lean_dec(x_10);
x_81 = !lean_is_exclusive(x_56);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_56, 0);
lean_dec(x_82);
x_83 = 1;
x_84 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_85 = l_Lean_Name_toString(x_9, x_83, x_84);
x_86 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_87 = lean_string_append(x_86, x_85);
lean_dec(x_85);
x_88 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_89 = lean_string_append(x_87, x_88);
lean_ctor_set_tag(x_56, 18);
lean_ctor_set(x_56, 0, x_89);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_56);
return x_16;
}
else
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_56);
x_90 = 1;
x_91 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_92 = l_Lean_Name_toString(x_9, x_90, x_91);
x_93 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_94 = lean_string_append(x_93, x_92);
lean_dec(x_92);
x_95 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_96 = lean_string_append(x_94, x_95);
x_97 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_97);
return x_16;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; size_t x_108; size_t x_109; size_t x_110; size_t x_111; size_t x_112; lean_object* x_113; lean_object* x_114; 
x_98 = lean_ctor_get(x_3, 1);
x_99 = lean_ctor_get(x_30, 0);
lean_inc(x_99);
lean_dec(x_30);
x_100 = lean_array_get_size(x_98);
x_101 = l_Lean_Name_hash___override(x_9);
x_102 = 32;
x_103 = lean_uint64_shift_right(x_101, x_102);
x_104 = lean_uint64_xor(x_101, x_103);
x_105 = 16;
x_106 = lean_uint64_shift_right(x_104, x_105);
x_107 = lean_uint64_xor(x_104, x_106);
x_108 = lean_uint64_to_usize(x_107);
x_109 = lean_usize_of_nat(x_100);
lean_dec(x_100);
x_110 = 1;
x_111 = lean_usize_sub(x_109, x_110);
x_112 = lean_usize_land(x_108, x_111);
x_113 = lean_array_uget(x_98, x_112);
x_114 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Environment_find_x3f___spec__5(x_9, x_113);
lean_dec(x_113);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_99);
lean_dec(x_10);
x_115 = 1;
x_116 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_117 = l_Lean_Name_toString(x_9, x_115, x_116);
x_118 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_119 = lean_string_append(x_118, x_117);
lean_dec(x_117);
x_120 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_121 = lean_string_append(x_119, x_120);
x_122 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_122);
return x_16;
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_114, 0);
lean_inc(x_123);
lean_dec(x_114);
if (lean_obj_tag(x_123) == 7)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
x_126 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3174_(x_99, x_124);
lean_dec(x_124);
lean_dec(x_99);
if (x_126 == 0)
{
uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_10);
x_127 = 1;
x_128 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_129 = l_Lean_Name_toString(x_9, x_127, x_128);
x_130 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
x_131 = lean_string_append(x_130, x_129);
lean_dec(x_129);
x_132 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_133 = lean_string_append(x_131, x_132);
if (lean_is_scalar(x_125)) {
 x_134 = lean_alloc_ctor(18, 1, 0);
} else {
 x_134 = x_125;
 lean_ctor_set_tag(x_134, 18);
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_134);
return x_16;
}
else
{
lean_object* x_135; 
lean_dec(x_125);
lean_free_object(x_16);
lean_dec(x_9);
x_135 = lean_box(0);
x_1 = x_10;
x_2 = x_135;
x_5 = x_19;
goto _start;
}
}
else
{
lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_99);
lean_dec(x_10);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_137 = x_123;
} else {
 lean_dec_ref(x_123);
 x_137 = lean_box(0);
}
x_138 = 1;
x_139 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_140 = l_Lean_Name_toString(x_9, x_138, x_139);
x_141 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_142 = lean_string_append(x_141, x_140);
lean_dec(x_140);
x_143 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_144 = lean_string_append(x_142, x_143);
if (lean_is_scalar(x_137)) {
 x_145 = lean_alloc_ctor(18, 1, 0);
} else {
 x_145 = x_137;
 lean_ctor_set_tag(x_145, 18);
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_145);
return x_16;
}
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_10);
x_146 = !lean_is_exclusive(x_30);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_147 = lean_ctor_get(x_30, 0);
lean_dec(x_147);
x_148 = 1;
x_149 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_150 = l_Lean_Name_toString(x_9, x_148, x_149);
x_151 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_152 = lean_string_append(x_151, x_150);
lean_dec(x_150);
x_153 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_154 = lean_string_append(x_152, x_153);
lean_ctor_set_tag(x_30, 18);
lean_ctor_set(x_30, 0, x_154);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
else
{
uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_30);
x_155 = 1;
x_156 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_157 = l_Lean_Name_toString(x_9, x_155, x_156);
x_158 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_159 = lean_string_append(x_158, x_157);
lean_dec(x_157);
x_160 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_161 = lean_string_append(x_159, x_160);
x_162 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_162);
return x_16;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_ctor_get(x_16, 0);
x_164 = lean_ctor_get(x_16, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_16);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_167 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_166, x_9);
if (lean_obj_tag(x_167) == 0)
{
uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_10);
x_168 = 1;
x_169 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_170 = l_Lean_Name_toString(x_9, x_168, x_169);
x_171 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_172 = lean_string_append(x_171, x_170);
lean_dec(x_170);
x_173 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_174 = lean_string_append(x_172, x_173);
lean_ctor_set_tag(x_12, 18);
lean_ctor_set(x_12, 0, x_174);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_12);
lean_ctor_set(x_175, 1, x_164);
return x_175;
}
else
{
lean_object* x_176; 
lean_free_object(x_12);
x_176 = lean_ctor_get(x_167, 0);
lean_inc(x_176);
lean_dec(x_167);
if (lean_obj_tag(x_176) == 7)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; uint64_t x_187; size_t x_188; size_t x_189; size_t x_190; size_t x_191; size_t x_192; lean_object* x_193; lean_object* x_194; 
x_177 = lean_ctor_get(x_3, 1);
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
x_180 = lean_array_get_size(x_177);
x_181 = l_Lean_Name_hash___override(x_9);
x_182 = 32;
x_183 = lean_uint64_shift_right(x_181, x_182);
x_184 = lean_uint64_xor(x_181, x_183);
x_185 = 16;
x_186 = lean_uint64_shift_right(x_184, x_185);
x_187 = lean_uint64_xor(x_184, x_186);
x_188 = lean_uint64_to_usize(x_187);
x_189 = lean_usize_of_nat(x_180);
lean_dec(x_180);
x_190 = 1;
x_191 = lean_usize_sub(x_189, x_190);
x_192 = lean_usize_land(x_188, x_191);
x_193 = lean_array_uget(x_177, x_192);
x_194 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Environment_find_x3f___spec__5(x_9, x_193);
lean_dec(x_193);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_178);
lean_dec(x_10);
x_195 = 1;
x_196 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_197 = l_Lean_Name_toString(x_9, x_195, x_196);
x_198 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_199 = lean_string_append(x_198, x_197);
lean_dec(x_197);
x_200 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_201 = lean_string_append(x_199, x_200);
if (lean_is_scalar(x_179)) {
 x_202 = lean_alloc_ctor(18, 1, 0);
} else {
 x_202 = x_179;
 lean_ctor_set_tag(x_202, 18);
}
lean_ctor_set(x_202, 0, x_201);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_164);
return x_203;
}
else
{
lean_object* x_204; 
lean_dec(x_179);
x_204 = lean_ctor_get(x_194, 0);
lean_inc(x_204);
lean_dec(x_194);
if (lean_obj_tag(x_204) == 7)
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
x_207 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3174_(x_178, x_205);
lean_dec(x_205);
lean_dec(x_178);
if (x_207 == 0)
{
uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_10);
x_208 = 1;
x_209 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_210 = l_Lean_Name_toString(x_9, x_208, x_209);
x_211 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
x_212 = lean_string_append(x_211, x_210);
lean_dec(x_210);
x_213 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_214 = lean_string_append(x_212, x_213);
if (lean_is_scalar(x_206)) {
 x_215 = lean_alloc_ctor(18, 1, 0);
} else {
 x_215 = x_206;
 lean_ctor_set_tag(x_215, 18);
}
lean_ctor_set(x_215, 0, x_214);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_164);
return x_216;
}
else
{
lean_object* x_217; 
lean_dec(x_206);
lean_dec(x_9);
x_217 = lean_box(0);
x_1 = x_10;
x_2 = x_217;
x_5 = x_164;
goto _start;
}
}
else
{
lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_178);
lean_dec(x_10);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_219 = x_204;
} else {
 lean_dec_ref(x_204);
 x_219 = lean_box(0);
}
x_220 = 1;
x_221 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_222 = l_Lean_Name_toString(x_9, x_220, x_221);
x_223 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_224 = lean_string_append(x_223, x_222);
lean_dec(x_222);
x_225 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_226 = lean_string_append(x_224, x_225);
if (lean_is_scalar(x_219)) {
 x_227 = lean_alloc_ctor(18, 1, 0);
} else {
 x_227 = x_219;
 lean_ctor_set_tag(x_227, 18);
}
lean_ctor_set(x_227, 0, x_226);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_164);
return x_228;
}
}
}
else
{
lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_10);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_229 = x_176;
} else {
 lean_dec_ref(x_176);
 x_229 = lean_box(0);
}
x_230 = 1;
x_231 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_232 = l_Lean_Name_toString(x_9, x_230, x_231);
x_233 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_234 = lean_string_append(x_233, x_232);
lean_dec(x_232);
x_235 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_236 = lean_string_append(x_234, x_235);
if (lean_is_scalar(x_229)) {
 x_237 = lean_alloc_ctor(18, 1, 0);
} else {
 x_237 = x_229;
 lean_ctor_set_tag(x_237, 18);
}
lean_ctor_set(x_237, 0, x_236);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_164);
return x_238;
}
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_12);
x_239 = lean_ctor_get(x_11, 1);
lean_inc(x_239);
lean_dec(x_11);
x_240 = lean_st_ref_get(x_4, x_239);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_241, 0);
lean_inc(x_244);
lean_dec(x_241);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec(x_244);
x_246 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_245, x_9);
if (lean_obj_tag(x_246) == 0)
{
uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_10);
x_247 = 1;
x_248 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_249 = l_Lean_Name_toString(x_9, x_247, x_248);
x_250 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_251 = lean_string_append(x_250, x_249);
lean_dec(x_249);
x_252 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_253 = lean_string_append(x_251, x_252);
x_254 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_254, 0, x_253);
if (lean_is_scalar(x_243)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_243;
 lean_ctor_set_tag(x_255, 1);
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_242);
return x_255;
}
else
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_246, 0);
lean_inc(x_256);
lean_dec(x_246);
if (lean_obj_tag(x_256) == 7)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint64_t x_261; uint64_t x_262; uint64_t x_263; uint64_t x_264; uint64_t x_265; uint64_t x_266; uint64_t x_267; size_t x_268; size_t x_269; size_t x_270; size_t x_271; size_t x_272; lean_object* x_273; lean_object* x_274; 
x_257 = lean_ctor_get(x_3, 1);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_259 = x_256;
} else {
 lean_dec_ref(x_256);
 x_259 = lean_box(0);
}
x_260 = lean_array_get_size(x_257);
x_261 = l_Lean_Name_hash___override(x_9);
x_262 = 32;
x_263 = lean_uint64_shift_right(x_261, x_262);
x_264 = lean_uint64_xor(x_261, x_263);
x_265 = 16;
x_266 = lean_uint64_shift_right(x_264, x_265);
x_267 = lean_uint64_xor(x_264, x_266);
x_268 = lean_uint64_to_usize(x_267);
x_269 = lean_usize_of_nat(x_260);
lean_dec(x_260);
x_270 = 1;
x_271 = lean_usize_sub(x_269, x_270);
x_272 = lean_usize_land(x_268, x_271);
x_273 = lean_array_uget(x_257, x_272);
x_274 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Environment_find_x3f___spec__5(x_9, x_273);
lean_dec(x_273);
if (lean_obj_tag(x_274) == 0)
{
uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_258);
lean_dec(x_10);
x_275 = 1;
x_276 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_277 = l_Lean_Name_toString(x_9, x_275, x_276);
x_278 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_279 = lean_string_append(x_278, x_277);
lean_dec(x_277);
x_280 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_281 = lean_string_append(x_279, x_280);
if (lean_is_scalar(x_259)) {
 x_282 = lean_alloc_ctor(18, 1, 0);
} else {
 x_282 = x_259;
 lean_ctor_set_tag(x_282, 18);
}
lean_ctor_set(x_282, 0, x_281);
if (lean_is_scalar(x_243)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_243;
 lean_ctor_set_tag(x_283, 1);
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_242);
return x_283;
}
else
{
lean_object* x_284; 
lean_dec(x_259);
x_284 = lean_ctor_get(x_274, 0);
lean_inc(x_284);
lean_dec(x_274);
if (lean_obj_tag(x_284) == 7)
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 x_286 = x_284;
} else {
 lean_dec_ref(x_284);
 x_286 = lean_box(0);
}
x_287 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3174_(x_258, x_285);
lean_dec(x_285);
lean_dec(x_258);
if (x_287 == 0)
{
uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_10);
x_288 = 1;
x_289 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_290 = l_Lean_Name_toString(x_9, x_288, x_289);
x_291 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
x_292 = lean_string_append(x_291, x_290);
lean_dec(x_290);
x_293 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_294 = lean_string_append(x_292, x_293);
if (lean_is_scalar(x_286)) {
 x_295 = lean_alloc_ctor(18, 1, 0);
} else {
 x_295 = x_286;
 lean_ctor_set_tag(x_295, 18);
}
lean_ctor_set(x_295, 0, x_294);
if (lean_is_scalar(x_243)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_243;
 lean_ctor_set_tag(x_296, 1);
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_242);
return x_296;
}
else
{
lean_object* x_297; 
lean_dec(x_286);
lean_dec(x_243);
lean_dec(x_9);
x_297 = lean_box(0);
x_1 = x_10;
x_2 = x_297;
x_5 = x_242;
goto _start;
}
}
else
{
lean_object* x_299; uint8_t x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_258);
lean_dec(x_10);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 x_299 = x_284;
} else {
 lean_dec_ref(x_284);
 x_299 = lean_box(0);
}
x_300 = 1;
x_301 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_302 = l_Lean_Name_toString(x_9, x_300, x_301);
x_303 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_304 = lean_string_append(x_303, x_302);
lean_dec(x_302);
x_305 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_306 = lean_string_append(x_304, x_305);
if (lean_is_scalar(x_299)) {
 x_307 = lean_alloc_ctor(18, 1, 0);
} else {
 x_307 = x_299;
 lean_ctor_set_tag(x_307, 18);
}
lean_ctor_set(x_307, 0, x_306);
if (lean_is_scalar(x_243)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_243;
 lean_ctor_set_tag(x_308, 1);
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_242);
return x_308;
}
}
}
else
{
lean_object* x_309; uint8_t x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_10);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_309 = x_256;
} else {
 lean_dec_ref(x_256);
 x_309 = lean_box(0);
}
x_310 = 1;
x_311 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_312 = l_Lean_Name_toString(x_9, x_310, x_311);
x_313 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_314 = lean_string_append(x_313, x_312);
lean_dec(x_312);
x_315 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_316 = lean_string_append(x_314, x_315);
if (lean_is_scalar(x_309)) {
 x_317 = lean_alloc_ctor(18, 1, 0);
} else {
 x_317 = x_309;
 lean_ctor_set_tag(x_317, 18);
}
lean_ctor_set(x_317, 0, x_316);
if (lean_is_scalar(x_243)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_243;
 lean_ctor_set_tag(x_318, 1);
}
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_242);
return x_318;
}
}
}
}
else
{
uint8_t x_319; 
lean_dec(x_10);
lean_dec(x_9);
x_319 = !lean_is_exclusive(x_11);
if (x_319 == 0)
{
return x_11;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_11, 0);
x_321 = lean_ctor_get(x_11, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_11);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 4);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1(x_7, x_8, x_1, x_2, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_checkPostponedRecursors(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Environment_replay___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_replay___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_ConstantInfo_isUnsafe(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_ConstantInfo_isPartial(x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_7, x_11);
x_1 = x_6;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
x_1 = x_6;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
x_1 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_replay___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Environment_replay___spec__1(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replay(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_box(0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
x_9 = x_4;
goto block_47;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_6, x_6);
if (x_48 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
x_9 = x_4;
goto block_47;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
x_49 = 0;
x_50 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_51 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_replay___spec__3(x_5, x_49, x_50, x_4);
lean_dec(x_5);
x_9 = x_51;
goto block_47;
}
}
block_47:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_40; lean_object* x_41; 
x_10 = l_Lean_NameSet_empty;
x_11 = l_List_forIn_loop___at_Lean_Environment_replay___spec__2(x_9, x_10, x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_10);
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_40 = lean_box(0);
lean_inc(x_16);
lean_inc(x_1);
x_41 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_replayConstants___spec__1(x_12, x_40, x_1, x_16, x_17);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_18 = x_42;
goto block_39;
}
else
{
uint8_t x_43; 
lean_dec(x_16);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_41);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
block_39:
{
lean_object* x_19; 
x_19 = l_Lean_Environment_Replay_checkPostponedConstructors(x_1, x_16, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Environment_Replay_checkPostponedRecursors(x_1, x_16, x_20);
lean_dec(x_1);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_16, x_22);
lean_dec(x_16);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_16);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_16);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Environment_replay___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Environment_replay___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_replay___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_replay___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Replay(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Environment_Replay_throwKernelException___lambda__1___closed__1 = _init_l_Lean_Environment_Replay_throwKernelException___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___lambda__1___closed__1);
l_Lean_Environment_Replay_throwKernelException___closed__1 = _init_l_Lean_Environment_Replay_throwKernelException___closed__1();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__1);
l_Lean_Environment_Replay_throwKernelException___closed__2 = _init_l_Lean_Environment_Replay_throwKernelException___closed__2();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__2);
l_Lean_Environment_Replay_throwKernelException___closed__3 = _init_l_Lean_Environment_Replay_throwKernelException___closed__3();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__3);
l_Lean_Environment_Replay_throwKernelException___closed__4 = _init_l_Lean_Environment_Replay_throwKernelException___closed__4();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__4);
l_Lean_Environment_Replay_throwKernelException___closed__5 = _init_l_Lean_Environment_Replay_throwKernelException___closed__5();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__5);
l_Lean_Environment_Replay_throwKernelException___closed__6 = _init_l_Lean_Environment_Replay_throwKernelException___closed__6();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__6);
l_Lean_Environment_Replay_throwKernelException___closed__7 = _init_l_Lean_Environment_Replay_throwKernelException___closed__7();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__7);
l_Lean_Environment_Replay_throwKernelException___closed__8 = _init_l_Lean_Environment_Replay_throwKernelException___closed__8();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__8);
l_Lean_Environment_Replay_throwKernelException___closed__9 = _init_l_Lean_Environment_Replay_throwKernelException___closed__9();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__9);
l_Lean_Environment_Replay_throwKernelException___closed__10 = _init_l_Lean_Environment_Replay_throwKernelException___closed__10();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__10);
l_Lean_Environment_Replay_throwKernelException___closed__11 = _init_l_Lean_Environment_Replay_throwKernelException___closed__11();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__11);
l_Lean_Environment_Replay_throwKernelException___closed__12 = _init_l_Lean_Environment_Replay_throwKernelException___closed__12();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__12);
l_Lean_Environment_Replay_throwKernelException___closed__13 = _init_l_Lean_Environment_Replay_throwKernelException___closed__13();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__13);
l_Lean_Environment_Replay_throwKernelException___closed__14 = _init_l_Lean_Environment_Replay_throwKernelException___closed__14();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__14);
l_Lean_Environment_Replay_throwKernelException___closed__15 = _init_l_Lean_Environment_Replay_throwKernelException___closed__15();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__15);
l_Lean_Environment_Replay_throwKernelException___closed__16 = _init_l_Lean_Environment_Replay_throwKernelException___closed__16();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__16);
l_Lean_Environment_Replay_throwKernelException___closed__17 = _init_l_Lean_Environment_Replay_throwKernelException___closed__17();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__17);
l_Lean_Environment_Replay_throwKernelException___closed__18 = _init_l_Lean_Environment_Replay_throwKernelException___closed__18();
lean_mark_persistent(l_Lean_Environment_Replay_throwKernelException___closed__18);
l_Lean_Environment_Replay_throwKernelException___closed__19 = _init_l_Lean_Environment_Replay_throwKernelException___closed__19();
l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__1 = _init_l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__1);
l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__2 = _init_l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__2);
l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__3 = _init_l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__3);
l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__4 = _init_l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__4();
lean_mark_persistent(l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__4);
l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__1 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__1();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__1);
l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__2 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__2();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__2);
l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__3 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__3();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__3);
l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__4 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__4();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at_Lean_Environment_Replay_replayConstant___spec__2___closed__4);
l_Lean_Environment_Replay_replayConstant___closed__1 = _init_l_Lean_Environment_Replay_replayConstant___closed__1();
lean_mark_persistent(l_Lean_Environment_Replay_replayConstant___closed__1);
l_Lean_Environment_Replay_replayConstant___closed__2 = _init_l_Lean_Environment_Replay_replayConstant___closed__2();
lean_mark_persistent(l_Lean_Environment_Replay_replayConstant___closed__2);
l_Lean_Environment_Replay_replayConstant___closed__3 = _init_l_Lean_Environment_Replay_replayConstant___closed__3();
lean_mark_persistent(l_Lean_Environment_Replay_replayConstant___closed__3);
l_Lean_Environment_Replay_replayConstant___closed__4 = _init_l_Lean_Environment_Replay_replayConstant___closed__4();
lean_mark_persistent(l_Lean_Environment_Replay_replayConstant___closed__4);
l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1 = _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1);
l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2 = _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2);
l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__3 = _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__3();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__3);
l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1 = _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1);
l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2 = _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
