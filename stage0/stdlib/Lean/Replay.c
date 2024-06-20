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
static lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__2;
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__15;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstant___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__3;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstant(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__12;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__7;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_State_postponedConstructors___default;
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Environment_replay___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__14;
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__6;
lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint8_t l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_2815_(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_replayConstant___closed__2;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_instInhabitedPUnit;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__4;
static lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_replay___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at_Lean_Environment_Replay_replayConstant___spec__9(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__5;
LEAN_EXPORT lean_object* l_Lean_Environment_replay(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstant___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_State_pending___default;
static lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__1;
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__13;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__1;
static lean_object* l_Lean_Environment_Replay_replayConstant___closed__4;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_State_remaining___default;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__9;
uint8_t l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3220_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__2(lean_object*);
lean_object* l_Lean_throwKernelException___at_Lean_addDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__18;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__1;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_toList___at_Lean_Environment_replay___spec__1___boxed(lean_object*);
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Lean_HashMap_toList___at_Lean_Environment_replay___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
static lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_addDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_replayConstants___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__17;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__2;
uint8_t l_Lean_RBNode_isBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_replay___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_State_postponedRecursors___default;
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__8;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstants(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__2;
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_replayConstant___closed__3;
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__11;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Environment_Replay_replayConstant___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
LEAN_EXPORT lean_object* l_List_map___at_Lean_Environment_Replay_replayConstant___spec__8(lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__10;
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Environment_replay___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
static lean_object* _init_l_Lean_Environment_Replay_State_remaining___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_State_pending___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_State_postponedConstructors___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_State_postponedRecursors___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Environment_Replay_throwKernelException___closed__12;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
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
x_10 = l_Lean_Environment_addDecl(x_8, x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Environment_Replay_throwKernelException(x_11, x_2, x_3, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_st_ref_take(x_3, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
lean_ctor_set(x_15, 0, x_13);
x_19 = lean_st_ref_set(x_3, x_15, x_16);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_15, 1);
x_27 = lean_ctor_get(x_15, 2);
x_28 = lean_ctor_get(x_15, 3);
x_29 = lean_ctor_get(x_15, 4);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set(x_30, 4, x_29);
x_31 = lean_st_ref_set(x_3, x_30, x_16);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedConstantInfo;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Data.HashMap", 17, 17);
return x_1;
}
}
static lean_object* _init_l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.HashMap.find!", 18, 18);
return x_1;
}
}
static lean_object* _init_l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key is not in the map", 21, 21);
return x_1;
}
}
static lean_object* _init_l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__1;
x_2 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__2;
x_3 = lean_unsigned_to_nat(221u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_List_reverse___rarg(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__4;
x_13 = l_panic___at_Lean_Environment_Replay_replayConstant___spec__2(x_12);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_13);
{
lean_object* _tmp_0 = x_10;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_15);
{
lean_object* _tmp_0 = x_10;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_17);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__4;
x_21 = l_panic___at_Lean_Environment_Replay_replayConstant___spec__2(x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
x_1 = x_18;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_2);
x_1 = x_18;
x_2 = x_25;
goto _start;
}
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_List_reverse___rarg(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = l_Lean_ConstantInfo_inductiveVal_x21(x_10);
x_13 = lean_ctor_get(x_12, 4);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_1);
x_14 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(x_13, x_1, x_4, x_5, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_ctor_set(x_14, 1, x_16);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_14);
{
lean_object* _tmp_1 = x_11;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_5 = x_17;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_21);
{
lean_object* _tmp_1 = x_11;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_5 = x_20;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_6 = _tmp_5;
}
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_25 = l_Lean_ConstantInfo_inductiveVal_x21(x_23);
x_26 = lean_ctor_get(x_25, 4);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_1);
x_27 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(x_26, x_1, x_4, x_5, x_6);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
x_2 = x_24;
x_3 = x_32;
x_6 = x_29;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__6(x_9, x_10, x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l_List_map___at_Lean_Environment_Replay_replayConstant___spec__8(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_ConstantInfo_name(x_4);
x_7 = l_Lean_ConstantInfo_type(x_4);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_List_map___at_Lean_Environment_Replay_replayConstant___spec__8(x_5);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Lean_ConstantInfo_name(x_10);
x_13 = l_Lean_ConstantInfo_type(x_10);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_List_map___at_Lean_Environment_Replay_replayConstant___spec__8(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at_Lean_Environment_Replay_replayConstant___spec__9(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_List_map___at_Lean_Environment_Replay_replayConstant___spec__9(x_5);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_ConstantInfo_name(x_7);
x_10 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_11 = l_List_map___at_Lean_Environment_Replay_replayConstant___spec__8(x_8);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_List_map___at_Lean_Environment_Replay_replayConstant___spec__9(x_14);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_ConstantInfo_name(x_16);
x_19 = l_Lean_ConstantInfo_type(x_16);
lean_dec(x_16);
x_20 = l_List_map___at_Lean_Environment_Replay_replayConstant___spec__8(x_17);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
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
x_4 = lean_unsigned_to_nat(54u);
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
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_2, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = l_Lean_Environment_Replay_replayConstant___closed__4;
x_17 = l_panic___at_Lean_Environment_Replay_replayConstant___spec__1(x_16, x_2, x_3, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_18);
x_19 = l_Lean_ConstantInfo_getUsedConstantsAsSet(x_18);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Lean_Environment_Replay_replayConstants(x_19, x_2, x_3, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_3, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_NameSet_contains(x_26, x_1);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_box(0);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
else
{
lean_free_object(x_22);
switch (lean_obj_tag(x_18)) {
case 0:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = l_Lean_Environment_Replay_addDecl(x_18, x_2, x_3, x_25);
lean_dec(x_18);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_31, x_2, x_3, x_32);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_31);
lean_dec(x_1);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_38);
lean_dec(x_18);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_Environment_Replay_addDecl(x_39, x_2, x_3, x_25);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_41, x_2, x_3, x_42);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_41);
lean_dec(x_1);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_46 = x_40;
} else {
 lean_dec_ref(x_40);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
case 1:
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_18);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = l_Lean_Environment_Replay_addDecl(x_18, x_2, x_3, x_25);
lean_dec(x_18);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_50, x_2, x_3, x_51);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_50);
lean_dec(x_1);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_18, 0);
lean_inc(x_57);
lean_dec(x_18);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l_Lean_Environment_Replay_addDecl(x_58, x_2, x_3, x_25);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_60, x_2, x_3, x_61);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_60);
lean_dec(x_1);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_65 = x_59;
} else {
 lean_dec_ref(x_59);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
case 2:
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = l_Lean_Environment_Replay_addDecl(x_18, x_2, x_3, x_25);
lean_dec(x_18);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_69, x_2, x_3, x_70);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_69);
lean_dec(x_1);
return x_71;
}
else
{
uint8_t x_72; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
return x_68;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_68, 0);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_68);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_18, 0);
lean_inc(x_76);
lean_dec(x_18);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l_Lean_Environment_Replay_addDecl(x_77, x_2, x_3, x_25);
lean_dec(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_79, x_2, x_3, x_80);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_79);
lean_dec(x_1);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_84 = x_78;
} else {
 lean_dec_ref(x_78);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
case 3:
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_18);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = l_Lean_Environment_Replay_addDecl(x_18, x_2, x_3, x_25);
lean_dec(x_18);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_88, x_2, x_3, x_89);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_88);
lean_dec(x_1);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
return x_87;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_87, 0);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_87);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_18, 0);
lean_inc(x_95);
lean_dec(x_18);
x_96 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l_Lean_Environment_Replay_addDecl(x_96, x_2, x_3, x_25);
lean_dec(x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_98, x_2, x_3, x_99);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_98);
lean_dec(x_1);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_97, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_103 = x_97;
} else {
 lean_dec_ref(x_97);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
case 4:
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_18);
x_105 = lean_box(4);
x_106 = l_Lean_Environment_Replay_addDecl(x_105, x_2, x_3, x_25);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_107, x_2, x_3, x_108);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_107);
lean_dec(x_1);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_106);
if (x_110 == 0)
{
return x_106;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_106, 0);
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_106);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
case 5:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_114 = lean_ctor_get(x_18, 0);
lean_inc(x_114);
lean_dec(x_18);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 3);
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_box(0);
x_120 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(x_117, x_119, x_2, x_3, x_25);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_box(0);
x_124 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__4(x_121, x_123, x_2, x_3, x_122);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5(x_119, x_121, x_119, x_2, x_3, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_127);
x_129 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__7(x_127, x_123, x_2, x_3, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = l_List_map___at_Lean_Environment_Replay_replayConstant___spec__9(x_127);
x_132 = 0;
x_133 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_133, 0, x_118);
lean_ctor_set(x_133, 1, x_116);
lean_ctor_set(x_133, 2, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*3, x_132);
x_134 = l_Lean_Environment_Replay_addDecl(x_133, x_2, x_3, x_130);
lean_dec(x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_135, x_2, x_3, x_136);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_135);
lean_dec(x_1);
return x_137;
}
else
{
uint8_t x_138; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_134);
if (x_138 == 0)
{
return x_134;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_134, 0);
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_134);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_127);
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_129);
if (x_142 == 0)
{
return x_129;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_129, 0);
x_144 = lean_ctor_get(x_129, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_129);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
case 6:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_146 = lean_ctor_get(x_18, 0);
lean_inc(x_146);
lean_dec(x_18);
x_147 = lean_st_ref_take(x_3, x_25);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = !lean_is_exclusive(x_148);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_151 = lean_ctor_get(x_148, 3);
x_152 = lean_ctor_get(x_146, 0);
lean_inc(x_152);
lean_dec(x_146);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_box(0);
x_155 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_151, x_153, x_154);
lean_ctor_set(x_148, 3, x_155);
x_156 = lean_st_ref_set(x_3, x_148, x_149);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_158 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_154, x_2, x_3, x_157);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_159 = lean_ctor_get(x_148, 0);
x_160 = lean_ctor_get(x_148, 1);
x_161 = lean_ctor_get(x_148, 2);
x_162 = lean_ctor_get(x_148, 3);
x_163 = lean_ctor_get(x_148, 4);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_148);
x_164 = lean_ctor_get(x_146, 0);
lean_inc(x_164);
lean_dec(x_146);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_box(0);
x_167 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_162, x_165, x_166);
x_168 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_168, 0, x_159);
lean_ctor_set(x_168, 1, x_160);
lean_ctor_set(x_168, 2, x_161);
lean_ctor_set(x_168, 3, x_167);
lean_ctor_set(x_168, 4, x_163);
x_169 = lean_st_ref_set(x_3, x_168, x_149);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_171 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_166, x_2, x_3, x_170);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_171;
}
}
default: 
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_172 = lean_ctor_get(x_18, 0);
lean_inc(x_172);
lean_dec(x_18);
x_173 = lean_st_ref_take(x_3, x_25);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = !lean_is_exclusive(x_174);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_177 = lean_ctor_get(x_174, 4);
x_178 = lean_ctor_get(x_172, 0);
lean_inc(x_178);
lean_dec(x_172);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_box(0);
x_181 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_177, x_179, x_180);
lean_ctor_set(x_174, 4, x_181);
x_182 = lean_st_ref_set(x_3, x_174, x_175);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_180, x_2, x_3, x_183);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_185 = lean_ctor_get(x_174, 0);
x_186 = lean_ctor_get(x_174, 1);
x_187 = lean_ctor_get(x_174, 2);
x_188 = lean_ctor_get(x_174, 3);
x_189 = lean_ctor_get(x_174, 4);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_174);
x_190 = lean_ctor_get(x_172, 0);
lean_inc(x_190);
lean_dec(x_172);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec(x_190);
x_192 = lean_box(0);
x_193 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_189, x_191, x_192);
x_194 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_194, 0, x_185);
lean_ctor_set(x_194, 1, x_186);
lean_ctor_set(x_194, 2, x_187);
lean_ctor_set(x_194, 3, x_188);
lean_ctor_set(x_194, 4, x_193);
x_195 = lean_st_ref_set(x_3, x_194, x_175);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_197 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_192, x_2, x_3, x_196);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_197;
}
}
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_198 = lean_ctor_get(x_22, 0);
x_199 = lean_ctor_get(x_22, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_22);
x_200 = lean_ctor_get(x_198, 2);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l_Lean_NameSet_contains(x_200, x_1);
lean_dec(x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_202 = lean_box(0);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_199);
return x_203;
}
else
{
switch (lean_obj_tag(x_18)) {
case 0:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_18, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_205 = x_18;
} else {
 lean_dec_ref(x_18);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(0, 1, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_204);
x_207 = l_Lean_Environment_Replay_addDecl(x_206, x_2, x_3, x_199);
lean_dec(x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_208, x_2, x_3, x_209);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_208);
lean_dec(x_1);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_211 = lean_ctor_get(x_207, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_207, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_213 = x_207;
} else {
 lean_dec_ref(x_207);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
case 1:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_18, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_216 = x_18;
} else {
 lean_dec_ref(x_18);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_215);
x_218 = l_Lean_Environment_Replay_addDecl(x_217, x_2, x_3, x_199);
lean_dec(x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_219, x_2, x_3, x_220);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_219);
lean_dec(x_1);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_222 = lean_ctor_get(x_218, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_218, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_224 = x_218;
} else {
 lean_dec_ref(x_218);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
}
case 2:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_18, 0);
lean_inc(x_226);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_227 = x_18;
} else {
 lean_dec_ref(x_18);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(2, 1, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_226);
x_229 = l_Lean_Environment_Replay_addDecl(x_228, x_2, x_3, x_199);
lean_dec(x_228);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_230, x_2, x_3, x_231);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_230);
lean_dec(x_1);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_233 = lean_ctor_get(x_229, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_229, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_235 = x_229;
} else {
 lean_dec_ref(x_229);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
}
case 3:
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_237 = lean_ctor_get(x_18, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_238 = x_18;
} else {
 lean_dec_ref(x_18);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(3, 1, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_237);
x_240 = l_Lean_Environment_Replay_addDecl(x_239, x_2, x_3, x_199);
lean_dec(x_239);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_241, x_2, x_3, x_242);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_241);
lean_dec(x_1);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_244 = lean_ctor_get(x_240, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_240, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_246 = x_240;
} else {
 lean_dec_ref(x_240);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
case 4:
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_18);
x_248 = lean_box(4);
x_249 = l_Lean_Environment_Replay_addDecl(x_248, x_2, x_3, x_199);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_250, x_2, x_3, x_251);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_250);
lean_dec(x_1);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_253 = lean_ctor_get(x_249, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_249, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_255 = x_249;
} else {
 lean_dec_ref(x_249);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
case 5:
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_257 = lean_ctor_get(x_18, 0);
lean_inc(x_257);
lean_dec(x_18);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_257, 3);
lean_inc(x_260);
lean_dec(x_257);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_dec(x_258);
x_262 = lean_box(0);
x_263 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(x_260, x_262, x_2, x_3, x_199);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
x_266 = lean_box(0);
x_267 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__4(x_264, x_266, x_2, x_3, x_265);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec(x_267);
x_269 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5(x_262, x_264, x_262, x_2, x_3, x_268);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_270);
x_272 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__7(x_270, x_266, x_2, x_3, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; 
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
lean_dec(x_272);
x_274 = l_List_map___at_Lean_Environment_Replay_replayConstant___spec__9(x_270);
x_275 = 0;
x_276 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_276, 0, x_261);
lean_ctor_set(x_276, 1, x_259);
lean_ctor_set(x_276, 2, x_274);
lean_ctor_set_uint8(x_276, sizeof(void*)*3, x_275);
x_277 = l_Lean_Environment_Replay_addDecl(x_276, x_2, x_3, x_273);
lean_dec(x_276);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_278, x_2, x_3, x_279);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_278);
lean_dec(x_1);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_281 = lean_ctor_get(x_277, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_277, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_283 = x_277;
} else {
 lean_dec_ref(x_277);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_270);
lean_dec(x_261);
lean_dec(x_259);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_285 = lean_ctor_get(x_272, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_272, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_287 = x_272;
} else {
 lean_dec_ref(x_272);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
case 6:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_289 = lean_ctor_get(x_18, 0);
lean_inc(x_289);
lean_dec(x_18);
x_290 = lean_st_ref_take(x_3, x_199);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_ctor_get(x_291, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_291, 2);
lean_inc(x_295);
x_296 = lean_ctor_get(x_291, 3);
lean_inc(x_296);
x_297 = lean_ctor_get(x_291, 4);
lean_inc(x_297);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 lean_ctor_release(x_291, 2);
 lean_ctor_release(x_291, 3);
 lean_ctor_release(x_291, 4);
 x_298 = x_291;
} else {
 lean_dec_ref(x_291);
 x_298 = lean_box(0);
}
x_299 = lean_ctor_get(x_289, 0);
lean_inc(x_299);
lean_dec(x_289);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
lean_dec(x_299);
x_301 = lean_box(0);
x_302 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_296, x_300, x_301);
if (lean_is_scalar(x_298)) {
 x_303 = lean_alloc_ctor(0, 5, 0);
} else {
 x_303 = x_298;
}
lean_ctor_set(x_303, 0, x_293);
lean_ctor_set(x_303, 1, x_294);
lean_ctor_set(x_303, 2, x_295);
lean_ctor_set(x_303, 3, x_302);
lean_ctor_set(x_303, 4, x_297);
x_304 = lean_st_ref_set(x_3, x_303, x_292);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec(x_304);
x_306 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_301, x_2, x_3, x_305);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_306;
}
default: 
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_307 = lean_ctor_get(x_18, 0);
lean_inc(x_307);
lean_dec(x_18);
x_308 = lean_st_ref_take(x_3, x_199);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_ctor_get(x_309, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_309, 1);
lean_inc(x_312);
x_313 = lean_ctor_get(x_309, 2);
lean_inc(x_313);
x_314 = lean_ctor_get(x_309, 3);
lean_inc(x_314);
x_315 = lean_ctor_get(x_309, 4);
lean_inc(x_315);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 lean_ctor_release(x_309, 2);
 lean_ctor_release(x_309, 3);
 lean_ctor_release(x_309, 4);
 x_316 = x_309;
} else {
 lean_dec_ref(x_309);
 x_316 = lean_box(0);
}
x_317 = lean_ctor_get(x_307, 0);
lean_inc(x_317);
lean_dec(x_307);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
lean_dec(x_317);
x_319 = lean_box(0);
x_320 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_315, x_318, x_319);
if (lean_is_scalar(x_316)) {
 x_321 = lean_alloc_ctor(0, 5, 0);
} else {
 x_321 = x_316;
}
lean_ctor_set(x_321, 0, x_311);
lean_ctor_set(x_321, 1, x_312);
lean_ctor_set(x_321, 2, x_313);
lean_ctor_set(x_321, 3, x_314);
lean_ctor_set(x_321, 4, x_320);
x_322 = lean_st_ref_set(x_3, x_321, x_310);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
lean_dec(x_322);
x_324 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_319, x_2, x_3, x_323);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_324;
}
}
}
}
}
else
{
uint8_t x_325; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_325 = !lean_is_exclusive(x_20);
if (x_325 == 0)
{
return x_20;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_20, 0);
x_327 = lean_ctor_get(x_20, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_20);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
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
lean_object* x_7; 
x_7 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_4, x_2);
lean_dec(x_4);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
return x_6;
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
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_11, x_2);
lean_dec(x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("No such constructor ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2() {
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
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_10);
x_23 = 1;
x_24 = l_Lean_Name_toString(x_9, x_23);
x_25 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_28 = lean_string_append(x_26, x_27);
lean_ctor_set_tag(x_12, 18);
lean_ctor_set(x_12, 0, x_28);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_29; 
lean_free_object(x_12);
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
if (lean_obj_tag(x_29) == 6)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_10);
x_33 = 1;
x_34 = l_Lean_Name_toString(x_9, x_33);
x_35 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_38 = lean_string_append(x_36, x_37);
lean_ctor_set_tag(x_29, 18);
lean_ctor_set(x_29, 0, x_38);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_29);
return x_16;
}
else
{
lean_object* x_39; 
lean_free_object(x_29);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
if (lean_obj_tag(x_39) == 6)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_2815_(x_31, x_41);
lean_dec(x_41);
lean_dec(x_31);
if (x_42 == 0)
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
x_43 = 1;
x_44 = l_Lean_Name_toString(x_9, x_43);
x_45 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_48 = lean_string_append(x_46, x_47);
lean_ctor_set_tag(x_39, 18);
lean_ctor_set(x_39, 0, x_48);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_39);
return x_16;
}
else
{
lean_object* x_49; 
lean_free_object(x_39);
lean_free_object(x_16);
lean_dec(x_9);
x_49 = lean_box(0);
x_1 = x_10;
x_2 = x_49;
x_5 = x_19;
goto _start;
}
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_39, 0);
lean_inc(x_51);
lean_dec(x_39);
x_52 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_2815_(x_31, x_51);
lean_dec(x_51);
lean_dec(x_31);
if (x_52 == 0)
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_10);
x_53 = 1;
x_54 = l_Lean_Name_toString(x_9, x_53);
x_55 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_59);
return x_16;
}
else
{
lean_object* x_60; 
lean_free_object(x_16);
lean_dec(x_9);
x_60 = lean_box(0);
x_1 = x_10;
x_2 = x_60;
x_5 = x_19;
goto _start;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_31);
lean_dec(x_10);
x_62 = !lean_is_exclusive(x_39);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_39, 0);
lean_dec(x_63);
x_64 = 1;
x_65 = l_Lean_Name_toString(x_9, x_64);
x_66 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_67 = lean_string_append(x_66, x_65);
lean_dec(x_65);
x_68 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_69 = lean_string_append(x_67, x_68);
lean_ctor_set_tag(x_39, 18);
lean_ctor_set(x_39, 0, x_69);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_39);
return x_16;
}
else
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_39);
x_70 = 1;
x_71 = l_Lean_Name_toString(x_9, x_70);
x_72 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_73 = lean_string_append(x_72, x_71);
lean_dec(x_71);
x_74 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_76);
return x_16;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_29, 0);
lean_inc(x_77);
lean_dec(x_29);
x_78 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_77);
lean_dec(x_10);
x_79 = 1;
x_80 = l_Lean_Name_toString(x_9, x_79);
x_81 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_82 = lean_string_append(x_81, x_80);
lean_dec(x_80);
x_83 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_85);
return x_16;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_78, 0);
lean_inc(x_86);
lean_dec(x_78);
if (lean_obj_tag(x_86) == 6)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_2815_(x_77, x_87);
lean_dec(x_87);
lean_dec(x_77);
if (x_89 == 0)
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_10);
x_90 = 1;
x_91 = l_Lean_Name_toString(x_9, x_90);
x_92 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_93 = lean_string_append(x_92, x_91);
lean_dec(x_91);
x_94 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_95 = lean_string_append(x_93, x_94);
if (lean_is_scalar(x_88)) {
 x_96 = lean_alloc_ctor(18, 1, 0);
} else {
 x_96 = x_88;
 lean_ctor_set_tag(x_96, 18);
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_96);
return x_16;
}
else
{
lean_object* x_97; 
lean_dec(x_88);
lean_free_object(x_16);
lean_dec(x_9);
x_97 = lean_box(0);
x_1 = x_10;
x_2 = x_97;
x_5 = x_19;
goto _start;
}
}
else
{
lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_77);
lean_dec(x_10);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_99 = x_86;
} else {
 lean_dec_ref(x_86);
 x_99 = lean_box(0);
}
x_100 = 1;
x_101 = l_Lean_Name_toString(x_9, x_100);
x_102 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_103 = lean_string_append(x_102, x_101);
lean_dec(x_101);
x_104 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_105 = lean_string_append(x_103, x_104);
if (lean_is_scalar(x_99)) {
 x_106 = lean_alloc_ctor(18, 1, 0);
} else {
 x_106 = x_99;
 lean_ctor_set_tag(x_106, 18);
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_106);
return x_16;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_10);
x_107 = !lean_is_exclusive(x_29);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_29, 0);
lean_dec(x_108);
x_109 = 1;
x_110 = l_Lean_Name_toString(x_9, x_109);
x_111 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_112 = lean_string_append(x_111, x_110);
lean_dec(x_110);
x_113 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_114 = lean_string_append(x_112, x_113);
lean_ctor_set_tag(x_29, 18);
lean_ctor_set(x_29, 0, x_114);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_29);
return x_16;
}
else
{
uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_29);
x_115 = 1;
x_116 = l_Lean_Name_toString(x_9, x_115);
x_117 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_118 = lean_string_append(x_117, x_116);
lean_dec(x_116);
x_119 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_120 = lean_string_append(x_118, x_119);
x_121 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_121);
return x_16;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_16, 0);
x_123 = lean_ctor_get(x_16, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_16);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_125, x_9);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_10);
x_127 = 1;
x_128 = l_Lean_Name_toString(x_9, x_127);
x_129 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_130 = lean_string_append(x_129, x_128);
lean_dec(x_128);
x_131 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_132 = lean_string_append(x_130, x_131);
lean_ctor_set_tag(x_12, 18);
lean_ctor_set(x_12, 0, x_132);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_12);
lean_ctor_set(x_133, 1, x_123);
return x_133;
}
else
{
lean_object* x_134; 
lean_free_object(x_12);
x_134 = lean_ctor_get(x_126, 0);
lean_inc(x_134);
lean_dec(x_126);
if (lean_obj_tag(x_134) == 6)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
x_137 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
if (lean_obj_tag(x_137) == 0)
{
uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_135);
lean_dec(x_10);
x_138 = 1;
x_139 = l_Lean_Name_toString(x_9, x_138);
x_140 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_141 = lean_string_append(x_140, x_139);
lean_dec(x_139);
x_142 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_143 = lean_string_append(x_141, x_142);
if (lean_is_scalar(x_136)) {
 x_144 = lean_alloc_ctor(18, 1, 0);
} else {
 x_144 = x_136;
 lean_ctor_set_tag(x_144, 18);
}
lean_ctor_set(x_144, 0, x_143);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_123);
return x_145;
}
else
{
lean_object* x_146; 
lean_dec(x_136);
x_146 = lean_ctor_get(x_137, 0);
lean_inc(x_146);
lean_dec(x_137);
if (lean_obj_tag(x_146) == 6)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
x_149 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_2815_(x_135, x_147);
lean_dec(x_147);
lean_dec(x_135);
if (x_149 == 0)
{
uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_10);
x_150 = 1;
x_151 = l_Lean_Name_toString(x_9, x_150);
x_152 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_153 = lean_string_append(x_152, x_151);
lean_dec(x_151);
x_154 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_155 = lean_string_append(x_153, x_154);
if (lean_is_scalar(x_148)) {
 x_156 = lean_alloc_ctor(18, 1, 0);
} else {
 x_156 = x_148;
 lean_ctor_set_tag(x_156, 18);
}
lean_ctor_set(x_156, 0, x_155);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_123);
return x_157;
}
else
{
lean_object* x_158; 
lean_dec(x_148);
lean_dec(x_9);
x_158 = lean_box(0);
x_1 = x_10;
x_2 = x_158;
x_5 = x_123;
goto _start;
}
}
else
{
lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_135);
lean_dec(x_10);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_160 = x_146;
} else {
 lean_dec_ref(x_146);
 x_160 = lean_box(0);
}
x_161 = 1;
x_162 = l_Lean_Name_toString(x_9, x_161);
x_163 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_164 = lean_string_append(x_163, x_162);
lean_dec(x_162);
x_165 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_166 = lean_string_append(x_164, x_165);
if (lean_is_scalar(x_160)) {
 x_167 = lean_alloc_ctor(18, 1, 0);
} else {
 x_167 = x_160;
 lean_ctor_set_tag(x_167, 18);
}
lean_ctor_set(x_167, 0, x_166);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_123);
return x_168;
}
}
}
else
{
lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_10);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_169 = x_134;
} else {
 lean_dec_ref(x_134);
 x_169 = lean_box(0);
}
x_170 = 1;
x_171 = l_Lean_Name_toString(x_9, x_170);
x_172 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_173 = lean_string_append(x_172, x_171);
lean_dec(x_171);
x_174 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_175 = lean_string_append(x_173, x_174);
if (lean_is_scalar(x_169)) {
 x_176 = lean_alloc_ctor(18, 1, 0);
} else {
 x_176 = x_169;
 lean_ctor_set_tag(x_176, 18);
}
lean_ctor_set(x_176, 0, x_175);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_123);
return x_177;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_12);
x_178 = lean_ctor_get(x_11, 1);
lean_inc(x_178);
lean_dec(x_11);
x_179 = lean_st_ref_get(x_4, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_182 = x_179;
} else {
 lean_dec_ref(x_179);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_180, 0);
lean_inc(x_183);
lean_dec(x_180);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_184, x_9);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_10);
x_186 = 1;
x_187 = l_Lean_Name_toString(x_9, x_186);
x_188 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_189 = lean_string_append(x_188, x_187);
lean_dec(x_187);
x_190 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_192, 0, x_191);
if (lean_is_scalar(x_182)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_182;
 lean_ctor_set_tag(x_193, 1);
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_181);
return x_193;
}
else
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_185, 0);
lean_inc(x_194);
lean_dec(x_185);
if (lean_obj_tag(x_194) == 6)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_196 = x_194;
} else {
 lean_dec_ref(x_194);
 x_196 = lean_box(0);
}
x_197 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
if (lean_obj_tag(x_197) == 0)
{
uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_195);
lean_dec(x_10);
x_198 = 1;
x_199 = l_Lean_Name_toString(x_9, x_198);
x_200 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_201 = lean_string_append(x_200, x_199);
lean_dec(x_199);
x_202 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_203 = lean_string_append(x_201, x_202);
if (lean_is_scalar(x_196)) {
 x_204 = lean_alloc_ctor(18, 1, 0);
} else {
 x_204 = x_196;
 lean_ctor_set_tag(x_204, 18);
}
lean_ctor_set(x_204, 0, x_203);
if (lean_is_scalar(x_182)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_182;
 lean_ctor_set_tag(x_205, 1);
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_181);
return x_205;
}
else
{
lean_object* x_206; 
lean_dec(x_196);
x_206 = lean_ctor_get(x_197, 0);
lean_inc(x_206);
lean_dec(x_197);
if (lean_obj_tag(x_206) == 6)
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
x_209 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_2815_(x_195, x_207);
lean_dec(x_207);
lean_dec(x_195);
if (x_209 == 0)
{
uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_10);
x_210 = 1;
x_211 = l_Lean_Name_toString(x_9, x_210);
x_212 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_213 = lean_string_append(x_212, x_211);
lean_dec(x_211);
x_214 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_215 = lean_string_append(x_213, x_214);
if (lean_is_scalar(x_208)) {
 x_216 = lean_alloc_ctor(18, 1, 0);
} else {
 x_216 = x_208;
 lean_ctor_set_tag(x_216, 18);
}
lean_ctor_set(x_216, 0, x_215);
if (lean_is_scalar(x_182)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_182;
 lean_ctor_set_tag(x_217, 1);
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_181);
return x_217;
}
else
{
lean_object* x_218; 
lean_dec(x_208);
lean_dec(x_182);
lean_dec(x_9);
x_218 = lean_box(0);
x_1 = x_10;
x_2 = x_218;
x_5 = x_181;
goto _start;
}
}
else
{
lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_195);
lean_dec(x_10);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_220 = x_206;
} else {
 lean_dec_ref(x_206);
 x_220 = lean_box(0);
}
x_221 = 1;
x_222 = l_Lean_Name_toString(x_9, x_221);
x_223 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_224 = lean_string_append(x_223, x_222);
lean_dec(x_222);
x_225 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_226 = lean_string_append(x_224, x_225);
if (lean_is_scalar(x_220)) {
 x_227 = lean_alloc_ctor(18, 1, 0);
} else {
 x_227 = x_220;
 lean_ctor_set_tag(x_227, 18);
}
lean_ctor_set(x_227, 0, x_226);
if (lean_is_scalar(x_182)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_182;
 lean_ctor_set_tag(x_228, 1);
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_181);
return x_228;
}
}
}
else
{
lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_10);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_229 = x_194;
} else {
 lean_dec_ref(x_194);
 x_229 = lean_box(0);
}
x_230 = 1;
x_231 = l_Lean_Name_toString(x_9, x_230);
x_232 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_233 = lean_string_append(x_232, x_231);
lean_dec(x_231);
x_234 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_235 = lean_string_append(x_233, x_234);
if (lean_is_scalar(x_229)) {
 x_236 = lean_alloc_ctor(18, 1, 0);
} else {
 x_236 = x_229;
 lean_ctor_set_tag(x_236, 18);
}
lean_ctor_set(x_236, 0, x_235);
if (lean_is_scalar(x_182)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_182;
 lean_ctor_set_tag(x_237, 1);
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_181);
return x_237;
}
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_10);
lean_dec(x_9);
x_238 = !lean_is_exclusive(x_11);
if (x_238 == 0)
{
return x_11;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_11, 0);
x_240 = lean_ctor_get(x_11, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_11);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
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
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_10);
x_23 = 1;
x_24 = l_Lean_Name_toString(x_9, x_23);
x_25 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_28 = lean_string_append(x_26, x_27);
lean_ctor_set_tag(x_12, 18);
lean_ctor_set(x_12, 0, x_28);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_29; 
lean_free_object(x_12);
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
if (lean_obj_tag(x_29) == 7)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_10);
x_33 = 1;
x_34 = l_Lean_Name_toString(x_9, x_33);
x_35 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_38 = lean_string_append(x_36, x_37);
lean_ctor_set_tag(x_29, 18);
lean_ctor_set(x_29, 0, x_38);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_29);
return x_16;
}
else
{
lean_object* x_39; 
lean_free_object(x_29);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
if (lean_obj_tag(x_39) == 7)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3220_(x_31, x_41);
lean_dec(x_41);
lean_dec(x_31);
if (x_42 == 0)
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
x_43 = 1;
x_44 = l_Lean_Name_toString(x_9, x_43);
x_45 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_48 = lean_string_append(x_46, x_47);
lean_ctor_set_tag(x_39, 18);
lean_ctor_set(x_39, 0, x_48);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_39);
return x_16;
}
else
{
lean_object* x_49; 
lean_free_object(x_39);
lean_free_object(x_16);
lean_dec(x_9);
x_49 = lean_box(0);
x_1 = x_10;
x_2 = x_49;
x_5 = x_19;
goto _start;
}
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_39, 0);
lean_inc(x_51);
lean_dec(x_39);
x_52 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3220_(x_31, x_51);
lean_dec(x_51);
lean_dec(x_31);
if (x_52 == 0)
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_10);
x_53 = 1;
x_54 = l_Lean_Name_toString(x_9, x_53);
x_55 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_59);
return x_16;
}
else
{
lean_object* x_60; 
lean_free_object(x_16);
lean_dec(x_9);
x_60 = lean_box(0);
x_1 = x_10;
x_2 = x_60;
x_5 = x_19;
goto _start;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_31);
lean_dec(x_10);
x_62 = !lean_is_exclusive(x_39);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_39, 0);
lean_dec(x_63);
x_64 = 1;
x_65 = l_Lean_Name_toString(x_9, x_64);
x_66 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_67 = lean_string_append(x_66, x_65);
lean_dec(x_65);
x_68 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_69 = lean_string_append(x_67, x_68);
lean_ctor_set_tag(x_39, 18);
lean_ctor_set(x_39, 0, x_69);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_39);
return x_16;
}
else
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_39);
x_70 = 1;
x_71 = l_Lean_Name_toString(x_9, x_70);
x_72 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_73 = lean_string_append(x_72, x_71);
lean_dec(x_71);
x_74 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_76);
return x_16;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_29, 0);
lean_inc(x_77);
lean_dec(x_29);
x_78 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_77);
lean_dec(x_10);
x_79 = 1;
x_80 = l_Lean_Name_toString(x_9, x_79);
x_81 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_82 = lean_string_append(x_81, x_80);
lean_dec(x_80);
x_83 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_85);
return x_16;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_78, 0);
lean_inc(x_86);
lean_dec(x_78);
if (lean_obj_tag(x_86) == 7)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3220_(x_77, x_87);
lean_dec(x_87);
lean_dec(x_77);
if (x_89 == 0)
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_10);
x_90 = 1;
x_91 = l_Lean_Name_toString(x_9, x_90);
x_92 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
x_93 = lean_string_append(x_92, x_91);
lean_dec(x_91);
x_94 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_95 = lean_string_append(x_93, x_94);
if (lean_is_scalar(x_88)) {
 x_96 = lean_alloc_ctor(18, 1, 0);
} else {
 x_96 = x_88;
 lean_ctor_set_tag(x_96, 18);
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_96);
return x_16;
}
else
{
lean_object* x_97; 
lean_dec(x_88);
lean_free_object(x_16);
lean_dec(x_9);
x_97 = lean_box(0);
x_1 = x_10;
x_2 = x_97;
x_5 = x_19;
goto _start;
}
}
else
{
lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_77);
lean_dec(x_10);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_99 = x_86;
} else {
 lean_dec_ref(x_86);
 x_99 = lean_box(0);
}
x_100 = 1;
x_101 = l_Lean_Name_toString(x_9, x_100);
x_102 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_103 = lean_string_append(x_102, x_101);
lean_dec(x_101);
x_104 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_105 = lean_string_append(x_103, x_104);
if (lean_is_scalar(x_99)) {
 x_106 = lean_alloc_ctor(18, 1, 0);
} else {
 x_106 = x_99;
 lean_ctor_set_tag(x_106, 18);
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_106);
return x_16;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_10);
x_107 = !lean_is_exclusive(x_29);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_29, 0);
lean_dec(x_108);
x_109 = 1;
x_110 = l_Lean_Name_toString(x_9, x_109);
x_111 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_112 = lean_string_append(x_111, x_110);
lean_dec(x_110);
x_113 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_114 = lean_string_append(x_112, x_113);
lean_ctor_set_tag(x_29, 18);
lean_ctor_set(x_29, 0, x_114);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_29);
return x_16;
}
else
{
uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_29);
x_115 = 1;
x_116 = l_Lean_Name_toString(x_9, x_115);
x_117 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_118 = lean_string_append(x_117, x_116);
lean_dec(x_116);
x_119 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_120 = lean_string_append(x_118, x_119);
x_121 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_121);
return x_16;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_16, 0);
x_123 = lean_ctor_get(x_16, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_16);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_125, x_9);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_10);
x_127 = 1;
x_128 = l_Lean_Name_toString(x_9, x_127);
x_129 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_130 = lean_string_append(x_129, x_128);
lean_dec(x_128);
x_131 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_132 = lean_string_append(x_130, x_131);
lean_ctor_set_tag(x_12, 18);
lean_ctor_set(x_12, 0, x_132);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_12);
lean_ctor_set(x_133, 1, x_123);
return x_133;
}
else
{
lean_object* x_134; 
lean_free_object(x_12);
x_134 = lean_ctor_get(x_126, 0);
lean_inc(x_134);
lean_dec(x_126);
if (lean_obj_tag(x_134) == 7)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
x_137 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
if (lean_obj_tag(x_137) == 0)
{
uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_135);
lean_dec(x_10);
x_138 = 1;
x_139 = l_Lean_Name_toString(x_9, x_138);
x_140 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_141 = lean_string_append(x_140, x_139);
lean_dec(x_139);
x_142 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_143 = lean_string_append(x_141, x_142);
if (lean_is_scalar(x_136)) {
 x_144 = lean_alloc_ctor(18, 1, 0);
} else {
 x_144 = x_136;
 lean_ctor_set_tag(x_144, 18);
}
lean_ctor_set(x_144, 0, x_143);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_123);
return x_145;
}
else
{
lean_object* x_146; 
lean_dec(x_136);
x_146 = lean_ctor_get(x_137, 0);
lean_inc(x_146);
lean_dec(x_137);
if (lean_obj_tag(x_146) == 7)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
x_149 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3220_(x_135, x_147);
lean_dec(x_147);
lean_dec(x_135);
if (x_149 == 0)
{
uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_10);
x_150 = 1;
x_151 = l_Lean_Name_toString(x_9, x_150);
x_152 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
x_153 = lean_string_append(x_152, x_151);
lean_dec(x_151);
x_154 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_155 = lean_string_append(x_153, x_154);
if (lean_is_scalar(x_148)) {
 x_156 = lean_alloc_ctor(18, 1, 0);
} else {
 x_156 = x_148;
 lean_ctor_set_tag(x_156, 18);
}
lean_ctor_set(x_156, 0, x_155);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_123);
return x_157;
}
else
{
lean_object* x_158; 
lean_dec(x_148);
lean_dec(x_9);
x_158 = lean_box(0);
x_1 = x_10;
x_2 = x_158;
x_5 = x_123;
goto _start;
}
}
else
{
lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_135);
lean_dec(x_10);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_160 = x_146;
} else {
 lean_dec_ref(x_146);
 x_160 = lean_box(0);
}
x_161 = 1;
x_162 = l_Lean_Name_toString(x_9, x_161);
x_163 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_164 = lean_string_append(x_163, x_162);
lean_dec(x_162);
x_165 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_166 = lean_string_append(x_164, x_165);
if (lean_is_scalar(x_160)) {
 x_167 = lean_alloc_ctor(18, 1, 0);
} else {
 x_167 = x_160;
 lean_ctor_set_tag(x_167, 18);
}
lean_ctor_set(x_167, 0, x_166);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_123);
return x_168;
}
}
}
else
{
lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_10);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_169 = x_134;
} else {
 lean_dec_ref(x_134);
 x_169 = lean_box(0);
}
x_170 = 1;
x_171 = l_Lean_Name_toString(x_9, x_170);
x_172 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_173 = lean_string_append(x_172, x_171);
lean_dec(x_171);
x_174 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_175 = lean_string_append(x_173, x_174);
if (lean_is_scalar(x_169)) {
 x_176 = lean_alloc_ctor(18, 1, 0);
} else {
 x_176 = x_169;
 lean_ctor_set_tag(x_176, 18);
}
lean_ctor_set(x_176, 0, x_175);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_123);
return x_177;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_12);
x_178 = lean_ctor_get(x_11, 1);
lean_inc(x_178);
lean_dec(x_11);
x_179 = lean_st_ref_get(x_4, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_182 = x_179;
} else {
 lean_dec_ref(x_179);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_180, 0);
lean_inc(x_183);
lean_dec(x_180);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_184, x_9);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_10);
x_186 = 1;
x_187 = l_Lean_Name_toString(x_9, x_186);
x_188 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_189 = lean_string_append(x_188, x_187);
lean_dec(x_187);
x_190 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_192, 0, x_191);
if (lean_is_scalar(x_182)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_182;
 lean_ctor_set_tag(x_193, 1);
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_181);
return x_193;
}
else
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_185, 0);
lean_inc(x_194);
lean_dec(x_185);
if (lean_obj_tag(x_194) == 7)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_196 = x_194;
} else {
 lean_dec_ref(x_194);
 x_196 = lean_box(0);
}
x_197 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
if (lean_obj_tag(x_197) == 0)
{
uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_195);
lean_dec(x_10);
x_198 = 1;
x_199 = l_Lean_Name_toString(x_9, x_198);
x_200 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_201 = lean_string_append(x_200, x_199);
lean_dec(x_199);
x_202 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_203 = lean_string_append(x_201, x_202);
if (lean_is_scalar(x_196)) {
 x_204 = lean_alloc_ctor(18, 1, 0);
} else {
 x_204 = x_196;
 lean_ctor_set_tag(x_204, 18);
}
lean_ctor_set(x_204, 0, x_203);
if (lean_is_scalar(x_182)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_182;
 lean_ctor_set_tag(x_205, 1);
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_181);
return x_205;
}
else
{
lean_object* x_206; 
lean_dec(x_196);
x_206 = lean_ctor_get(x_197, 0);
lean_inc(x_206);
lean_dec(x_197);
if (lean_obj_tag(x_206) == 7)
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
x_209 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3220_(x_195, x_207);
lean_dec(x_207);
lean_dec(x_195);
if (x_209 == 0)
{
uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_10);
x_210 = 1;
x_211 = l_Lean_Name_toString(x_9, x_210);
x_212 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
x_213 = lean_string_append(x_212, x_211);
lean_dec(x_211);
x_214 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_215 = lean_string_append(x_213, x_214);
if (lean_is_scalar(x_208)) {
 x_216 = lean_alloc_ctor(18, 1, 0);
} else {
 x_216 = x_208;
 lean_ctor_set_tag(x_216, 18);
}
lean_ctor_set(x_216, 0, x_215);
if (lean_is_scalar(x_182)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_182;
 lean_ctor_set_tag(x_217, 1);
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_181);
return x_217;
}
else
{
lean_object* x_218; 
lean_dec(x_208);
lean_dec(x_182);
lean_dec(x_9);
x_218 = lean_box(0);
x_1 = x_10;
x_2 = x_218;
x_5 = x_181;
goto _start;
}
}
else
{
lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_195);
lean_dec(x_10);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_220 = x_206;
} else {
 lean_dec_ref(x_206);
 x_220 = lean_box(0);
}
x_221 = 1;
x_222 = l_Lean_Name_toString(x_9, x_221);
x_223 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_224 = lean_string_append(x_223, x_222);
lean_dec(x_222);
x_225 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_226 = lean_string_append(x_224, x_225);
if (lean_is_scalar(x_220)) {
 x_227 = lean_alloc_ctor(18, 1, 0);
} else {
 x_227 = x_220;
 lean_ctor_set_tag(x_227, 18);
}
lean_ctor_set(x_227, 0, x_226);
if (lean_is_scalar(x_182)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_182;
 lean_ctor_set_tag(x_228, 1);
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_181);
return x_228;
}
}
}
else
{
lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_10);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_229 = x_194;
} else {
 lean_dec_ref(x_194);
 x_229 = lean_box(0);
}
x_230 = 1;
x_231 = l_Lean_Name_toString(x_9, x_230);
x_232 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_233 = lean_string_append(x_232, x_231);
lean_dec(x_231);
x_234 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_235 = lean_string_append(x_233, x_234);
if (lean_is_scalar(x_229)) {
 x_236 = lean_alloc_ctor(18, 1, 0);
} else {
 x_236 = x_229;
 lean_ctor_set_tag(x_236, 18);
}
lean_ctor_set(x_236, 0, x_235);
if (lean_is_scalar(x_182)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_182;
 lean_ctor_set_tag(x_237, 1);
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_181);
return x_237;
}
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_10);
lean_dec(x_9);
x_238 = !lean_is_exclusive(x_11);
if (x_238 == 0)
{
return x_11;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_11, 0);
x_240 = lean_ctor_get(x_11, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_11);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Environment_replay___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_replay___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_AssocList_foldlM___at_Lean_Environment_replay___spec__2(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMap_toList___at_Lean_Environment_replay___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_replay___spec__3(x_3, x_8, x_9, x_2);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_replay___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Environment_replay(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_35; lean_object* x_36; 
x_4 = l_Lean_HashMap_toList___at_Lean_Environment_replay___spec__1(x_1);
x_5 = l_Lean_NameSet_empty;
x_6 = l_List_forIn_loop___at_Lean_Environment_replay___spec__4(x_4, x_5, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_5);
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_35 = lean_box(0);
lean_inc(x_11);
lean_inc(x_1);
x_36 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_replayConstants___spec__1(x_7, x_35, x_1, x_11, x_12);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_13 = x_37;
goto block_34;
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
block_34:
{
lean_object* x_14; 
x_14 = l_Lean_Environment_Replay_checkPostponedConstructors(x_1, x_11, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Environment_Replay_checkPostponedRecursors(x_1, x_11, x_15);
lean_dec(x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_11, x_17);
lean_dec(x_11);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Environment_replay___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_foldlM___at_Lean_Environment_replay___spec__2(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_HashMap_toList___at_Lean_Environment_replay___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_HashMap_toList___at_Lean_Environment_replay___spec__1(x_1);
lean_dec(x_1);
return x_2;
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
l_Lean_Environment_Replay_State_remaining___default = _init_l_Lean_Environment_Replay_State_remaining___default();
lean_mark_persistent(l_Lean_Environment_Replay_State_remaining___default);
l_Lean_Environment_Replay_State_pending___default = _init_l_Lean_Environment_Replay_State_pending___default();
lean_mark_persistent(l_Lean_Environment_Replay_State_pending___default);
l_Lean_Environment_Replay_State_postponedConstructors___default = _init_l_Lean_Environment_Replay_State_postponedConstructors___default();
lean_mark_persistent(l_Lean_Environment_Replay_State_postponedConstructors___default);
l_Lean_Environment_Replay_State_postponedRecursors___default = _init_l_Lean_Environment_Replay_State_postponedRecursors___default();
lean_mark_persistent(l_Lean_Environment_Replay_State_postponedRecursors___default);
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
l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__1 = _init_l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__1();
lean_mark_persistent(l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__1);
l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__2 = _init_l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__2();
lean_mark_persistent(l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__2);
l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__3 = _init_l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__3();
lean_mark_persistent(l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__3);
l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__4 = _init_l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__4();
lean_mark_persistent(l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__4);
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
l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1 = _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1);
l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2 = _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
