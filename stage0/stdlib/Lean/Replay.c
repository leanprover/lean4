// Lean compiler output
// Module: Lean.Replay
// Imports: Init Lean.CoreM Lean.Util.FoldConsts
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
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__14;
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__6;
lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonadEStateM(lean_object*, lean_object*);
lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_replayConstant___closed__2;
extern lean_object* l_instInhabitedPUnit;
static lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__4;
static lean_object* l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_replay___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Environment_Replay_throwKernelException___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__9;
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__2(lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__18;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_1830_(lean_object*, lean_object*);
uint8_t l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_2226_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_toList___at_Lean_Environment_replay___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
static lean_object* l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_replayConstants___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__17;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Environment_Replay_isTodo___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Environment_Replay_isTodo___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Environment_Replay_throwKernelException___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__4;
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__16;
extern lean_object* l_Lean_instInhabitedConstantInfo;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_replay___spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Environment_Replay_throwKernelException___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Environment_Replay_throwKernelException___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_throwKernelException___closed__10;
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Environment_replay___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Environment_Replay_throwKernelException___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Environment_Replay_throwKernelException___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_KernelException_toMessageData(x_1, x_5);
x_7 = l_Lean_throwError___at_Lean_Environment_Replay_throwKernelException___spec__2(x_6, x_2, x_3, x_4);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_2 = l_Lean_Environment_Replay_throwKernelException___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_uniq", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Environment_Replay_throwKernelException___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Environment_Replay_throwKernelException___closed__7;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Environment_Replay_throwKernelException___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__11() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Environment_Replay_throwKernelException___closed__10;
x_3 = l_Lean_Environment_Replay_throwKernelException___closed__9;
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
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Environment_Replay_throwKernelException___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Environment_Replay_throwKernelException___closed__13;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Environment_Replay_throwKernelException___closed__13;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Environment_Replay_throwKernelException___closed__17() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Environment_Replay_throwKernelException___closed__16;
x_3 = l_Lean_Environment_Replay_throwKernelException___closed__11;
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
x_1 = lean_mk_string_from_bytes("internal exception #", 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_5 = lean_box(0);
x_6 = lean_st_ref_get(x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Environment_Replay_throwKernelException___closed__5;
x_11 = l_Lean_Environment_Replay_throwKernelException___closed__8;
x_12 = l_Lean_Environment_Replay_throwKernelException___closed__11;
x_13 = l_Lean_Environment_Replay_throwKernelException___closed__15;
x_14 = l_Lean_Environment_Replay_throwKernelException___closed__17;
x_15 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set(x_15, 5, x_12);
lean_ctor_set(x_15, 6, x_14);
x_16 = lean_io_get_num_heartbeats(x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_20 = l_Lean_Environment_Replay_throwKernelException___closed__3;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_unsigned_to_nat(1000u);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = l_Lean_Environment_Replay_throwKernelException___closed__4;
x_26 = l_Lean_firstFrontendMacroScope;
x_27 = 0;
x_28 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_5);
lean_ctor_set(x_28, 3, x_21);
lean_ctor_set(x_28, 4, x_22);
lean_ctor_set(x_28, 5, x_23);
lean_ctor_set(x_28, 6, x_24);
lean_ctor_set(x_28, 7, x_5);
lean_ctor_set(x_28, 8, x_17);
lean_ctor_set(x_28, 9, x_25);
lean_ctor_set(x_28, 10, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*11, x_27);
x_29 = lean_st_mk_ref(x_15, x_18);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_throwKernelException___at_Lean_Environment_Replay_throwKernelException___spec__1(x_1, x_28, x_30, x_31);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_MessageData_toString(x_35, x_34);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_36);
if (x_44 == 0)
{
return x_36;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_36, 0);
x_46 = lean_ctor_get(x_36, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_36);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Environment_Replay_throwKernelException___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Environment_Replay_throwKernelException___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Environment_Replay_throwKernelException___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwKernelException___at_Lean_Environment_Replay_throwKernelException___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_add_decl(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Environment_Replay_throwKernelException(x_10, x_2, x_3, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_st_ref_take(x_3, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_18 = lean_st_ref_set(x_3, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_14, 1);
x_26 = lean_ctor_get(x_14, 2);
x_27 = lean_ctor_get(x_14, 3);
x_28 = lean_ctor_get(x_14, 4);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
x_30 = lean_st_ref_set(x_3, x_29, x_15);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
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
x_1 = l_EStateM_instMonadEStateM(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Environment_Replay_replayConstant___spec__1___closed__2;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
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
x_1 = lean_mk_string_from_bytes("Lean.Data.HashMap", 17);
return x_1;
}
}
static lean_object* _init_l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.HashMap.find!", 18);
return x_1;
}
}
static lean_object* _init_l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("key is not in the map", 21);
return x_1;
}
}
static lean_object* _init_l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__1;
x_2 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3___closed__2;
x_3 = lean_unsigned_to_nat(182u);
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
lean_dec(x_3);
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
lean_inc(x_3);
x_11 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
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
lean_inc(x_3);
x_19 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_17);
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
lean_dec(x_4);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_12 = l_Lean_ConstantInfo_inductiveVal_x21(x_10);
x_13 = lean_ctor_get(x_12, 4);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_4);
lean_inc(x_1);
x_14 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(x_13, x_1, x_4, x_5, x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_17);
{
lean_object* _tmp_1 = x_11;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_5 = x_16;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
lean_inc(x_19);
x_21 = l_Lean_ConstantInfo_inductiveVal_x21(x_19);
x_22 = lean_ctor_get(x_21, 4);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_4);
lean_inc(x_1);
x_23 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(x_22, x_1, x_4, x_5, x_6);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
x_2 = x_20;
x_3 = x_27;
x_6 = x_25;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__8(lean_object* x_1, lean_object* x_2) {
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
x_12 = l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__8(x_8, x_11);
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
x_22 = l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__8(x_18, x_21);
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
x_1 = lean_mk_string_from_bytes("Lean.Replay", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_replayConstant___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Environment.Replay.replayConstant", 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_replayConstant___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_replayConstant___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Environment_Replay_replayConstant___closed__1;
x_2 = l_Lean_Environment_Replay_replayConstant___closed__2;
x_3 = lean_unsigned_to_nat(74u);
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
lean_inc(x_1);
lean_inc(x_2);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_Environment_Replay_addDecl(x_30, x_2, x_3, x_25);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_32, x_2, x_3, x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_32);
lean_dec(x_1);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 1:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_18, 0);
lean_inc(x_39);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_Environment_Replay_addDecl(x_40, x_2, x_3, x_25);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_42, x_2, x_3, x_43);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_42);
lean_dec(x_1);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
case 2:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_18, 0);
lean_inc(x_49);
lean_dec(x_18);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_Environment_Replay_addDecl(x_50, x_2, x_3, x_25);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_52, x_2, x_3, x_53);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_52);
lean_dec(x_1);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 0);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_51);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
case 3:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_18, 0);
lean_inc(x_59);
lean_dec(x_18);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_Environment_Replay_addDecl(x_60, x_2, x_3, x_25);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_62, x_2, x_3, x_63);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_62);
lean_dec(x_1);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 4:
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_18);
x_69 = lean_box(4);
x_70 = l_Lean_Environment_Replay_addDecl(x_69, x_2, x_3, x_25);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_71, x_2, x_3, x_72);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_71);
lean_dec(x_1);
return x_73;
}
else
{
uint8_t x_74; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
return x_70;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_70, 0);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_70);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
case 5:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_78 = lean_ctor_get(x_18, 0);
lean_inc(x_78);
lean_dec(x_18);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 3);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_box(0);
lean_inc(x_2);
x_84 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(x_81, x_83, x_2, x_3, x_25);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_box(0);
x_88 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__4(x_85, x_87, x_2, x_3, x_86);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
lean_inc(x_2);
x_90 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5(x_83, x_85, x_83, x_2, x_3, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_91);
x_93 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__7(x_91, x_87, x_2, x_3, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__9(x_91, x_83);
x_96 = 0;
x_97 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_97, 0, x_82);
lean_ctor_set(x_97, 1, x_80);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*3, x_96);
x_98 = l_Lean_Environment_Replay_addDecl(x_97, x_2, x_3, x_94);
lean_dec(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_99, x_2, x_3, x_100);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_99);
lean_dec(x_1);
return x_101;
}
else
{
uint8_t x_102; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_98);
if (x_102 == 0)
{
return x_98;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_98, 0);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_98);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_91);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_93);
if (x_106 == 0)
{
return x_93;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_93, 0);
x_108 = lean_ctor_get(x_93, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_93);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
case 6:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_110 = lean_ctor_get(x_18, 0);
lean_inc(x_110);
lean_dec(x_18);
x_111 = lean_st_ref_take(x_3, x_25);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = !lean_is_exclusive(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_115 = lean_ctor_get(x_112, 3);
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
lean_dec(x_110);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_box(0);
x_119 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_115, x_117, x_118);
lean_ctor_set(x_112, 3, x_119);
x_120 = lean_st_ref_set(x_3, x_112, x_113);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_118, x_2, x_3, x_121);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_123 = lean_ctor_get(x_112, 0);
x_124 = lean_ctor_get(x_112, 1);
x_125 = lean_ctor_get(x_112, 2);
x_126 = lean_ctor_get(x_112, 3);
x_127 = lean_ctor_get(x_112, 4);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_112);
x_128 = lean_ctor_get(x_110, 0);
lean_inc(x_128);
lean_dec(x_110);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_box(0);
x_131 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_126, x_129, x_130);
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_123);
lean_ctor_set(x_132, 1, x_124);
lean_ctor_set(x_132, 2, x_125);
lean_ctor_set(x_132, 3, x_131);
lean_ctor_set(x_132, 4, x_127);
x_133 = lean_st_ref_set(x_3, x_132, x_113);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_130, x_2, x_3, x_134);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_135;
}
}
default: 
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_18, 0);
lean_inc(x_136);
lean_dec(x_18);
x_137 = lean_st_ref_take(x_3, x_25);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = !lean_is_exclusive(x_138);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_138, 4);
x_142 = lean_ctor_get(x_136, 0);
lean_inc(x_142);
lean_dec(x_136);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_box(0);
x_145 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_141, x_143, x_144);
lean_ctor_set(x_138, 4, x_145);
x_146 = lean_st_ref_set(x_3, x_138, x_139);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_148 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_144, x_2, x_3, x_147);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_149 = lean_ctor_get(x_138, 0);
x_150 = lean_ctor_get(x_138, 1);
x_151 = lean_ctor_get(x_138, 2);
x_152 = lean_ctor_get(x_138, 3);
x_153 = lean_ctor_get(x_138, 4);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_138);
x_154 = lean_ctor_get(x_136, 0);
lean_inc(x_154);
lean_dec(x_136);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_box(0);
x_157 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_153, x_155, x_156);
x_158 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_158, 0, x_149);
lean_ctor_set(x_158, 1, x_150);
lean_ctor_set(x_158, 2, x_151);
lean_ctor_set(x_158, 3, x_152);
lean_ctor_set(x_158, 4, x_157);
x_159 = lean_st_ref_set(x_3, x_158, x_139);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_161 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_156, x_2, x_3, x_160);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_161;
}
}
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_162 = lean_ctor_get(x_22, 0);
x_163 = lean_ctor_get(x_22, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_22);
x_164 = lean_ctor_get(x_162, 2);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_NameSet_contains(x_164, x_1);
lean_dec(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_163);
return x_167;
}
else
{
switch (lean_obj_tag(x_18)) {
case 0:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_18, 0);
lean_inc(x_168);
lean_dec(x_18);
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = l_Lean_Environment_Replay_addDecl(x_169, x_2, x_3, x_163);
lean_dec(x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_171, x_2, x_3, x_172);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_171);
lean_dec(x_1);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = lean_ctor_get(x_170, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_170, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_176 = x_170;
} else {
 lean_dec_ref(x_170);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
case 1:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_18, 0);
lean_inc(x_178);
lean_dec(x_18);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = l_Lean_Environment_Replay_addDecl(x_179, x_2, x_3, x_163);
lean_dec(x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_181, x_2, x_3, x_182);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_181);
lean_dec(x_1);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_184 = lean_ctor_get(x_180, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_180, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_186 = x_180;
} else {
 lean_dec_ref(x_180);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
case 2:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_18, 0);
lean_inc(x_188);
lean_dec(x_18);
x_189 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = l_Lean_Environment_Replay_addDecl(x_189, x_2, x_3, x_163);
lean_dec(x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_191, x_2, x_3, x_192);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_191);
lean_dec(x_1);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = lean_ctor_get(x_190, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_190, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_196 = x_190;
} else {
 lean_dec_ref(x_190);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
case 3:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_18, 0);
lean_inc(x_198);
lean_dec(x_18);
x_199 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_200 = l_Lean_Environment_Replay_addDecl(x_199, x_2, x_3, x_163);
lean_dec(x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_201, x_2, x_3, x_202);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_201);
lean_dec(x_1);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_204 = lean_ctor_get(x_200, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_200, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_206 = x_200;
} else {
 lean_dec_ref(x_200);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
case 4:
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_18);
x_208 = lean_box(4);
x_209 = l_Lean_Environment_Replay_addDecl(x_208, x_2, x_3, x_163);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_210, x_2, x_3, x_211);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_210);
lean_dec(x_1);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_ctor_get(x_209, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_209, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_215 = x_209;
} else {
 lean_dec_ref(x_209);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
case 5:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_217 = lean_ctor_get(x_18, 0);
lean_inc(x_217);
lean_dec(x_18);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_217, 3);
lean_inc(x_220);
lean_dec(x_217);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = lean_box(0);
lean_inc(x_2);
x_223 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__3(x_220, x_222, x_2, x_3, x_163);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_box(0);
x_227 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__4(x_224, x_226, x_2, x_3, x_225);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
lean_inc(x_2);
x_229 = l_List_mapM_loop___at_Lean_Environment_Replay_replayConstant___spec__5(x_222, x_224, x_222, x_2, x_3, x_228);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_230);
x_232 = l_List_forIn_loop___at_Lean_Environment_Replay_replayConstant___spec__7(x_230, x_226, x_2, x_3, x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
x_234 = l_List_mapTR_loop___at_Lean_Environment_Replay_replayConstant___spec__9(x_230, x_222);
x_235 = 0;
x_236 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_236, 0, x_221);
lean_ctor_set(x_236, 1, x_219);
lean_ctor_set(x_236, 2, x_234);
lean_ctor_set_uint8(x_236, sizeof(void*)*3, x_235);
x_237 = l_Lean_Environment_Replay_addDecl(x_236, x_2, x_3, x_233);
lean_dec(x_236);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_238, x_2, x_3, x_239);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_238);
lean_dec(x_1);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_241 = lean_ctor_get(x_237, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_237, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_243 = x_237;
} else {
 lean_dec_ref(x_237);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_230);
lean_dec(x_221);
lean_dec(x_219);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_245 = lean_ctor_get(x_232, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_232, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_247 = x_232;
} else {
 lean_dec_ref(x_232);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
case 6:
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_249 = lean_ctor_get(x_18, 0);
lean_inc(x_249);
lean_dec(x_18);
x_250 = lean_st_ref_take(x_3, x_163);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_251, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_251, 3);
lean_inc(x_256);
x_257 = lean_ctor_get(x_251, 4);
lean_inc(x_257);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 lean_ctor_release(x_251, 2);
 lean_ctor_release(x_251, 3);
 lean_ctor_release(x_251, 4);
 x_258 = x_251;
} else {
 lean_dec_ref(x_251);
 x_258 = lean_box(0);
}
x_259 = lean_ctor_get(x_249, 0);
lean_inc(x_259);
lean_dec(x_249);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
lean_dec(x_259);
x_261 = lean_box(0);
x_262 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_256, x_260, x_261);
if (lean_is_scalar(x_258)) {
 x_263 = lean_alloc_ctor(0, 5, 0);
} else {
 x_263 = x_258;
}
lean_ctor_set(x_263, 0, x_253);
lean_ctor_set(x_263, 1, x_254);
lean_ctor_set(x_263, 2, x_255);
lean_ctor_set(x_263, 3, x_262);
lean_ctor_set(x_263, 4, x_257);
x_264 = lean_st_ref_set(x_3, x_263, x_252);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
x_266 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_261, x_2, x_3, x_265);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_266;
}
default: 
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_267 = lean_ctor_get(x_18, 0);
lean_inc(x_267);
lean_dec(x_18);
x_268 = lean_st_ref_take(x_3, x_163);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_269, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_269, 2);
lean_inc(x_273);
x_274 = lean_ctor_get(x_269, 3);
lean_inc(x_274);
x_275 = lean_ctor_get(x_269, 4);
lean_inc(x_275);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 lean_ctor_release(x_269, 2);
 lean_ctor_release(x_269, 3);
 lean_ctor_release(x_269, 4);
 x_276 = x_269;
} else {
 lean_dec_ref(x_269);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_267, 0);
lean_inc(x_277);
lean_dec(x_267);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
lean_dec(x_277);
x_279 = lean_box(0);
x_280 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_275, x_278, x_279);
if (lean_is_scalar(x_276)) {
 x_281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_281 = x_276;
}
lean_ctor_set(x_281, 0, x_271);
lean_ctor_set(x_281, 1, x_272);
lean_ctor_set(x_281, 2, x_273);
lean_ctor_set(x_281, 3, x_274);
lean_ctor_set(x_281, 4, x_280);
x_282 = lean_st_ref_set(x_3, x_281, x_270);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_284 = l_Lean_Environment_Replay_replayConstant___lambda__1(x_1, x_279, x_2, x_3, x_283);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_284;
}
}
}
}
}
else
{
uint8_t x_285; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_285 = !lean_is_exclusive(x_20);
if (x_285 == 0)
{
return x_20;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_20, 0);
x_287 = lean_ctor_get(x_20, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_20);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
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
lean_inc(x_2);
x_6 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Environment_find_x3f___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_4, x_2);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_2);
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
return x_12;
}
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("No such constructor ", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Invalid constructor ", 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
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
lean_inc(x_3);
x_11 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_9);
x_19 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_18, x_9);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_3);
x_20 = 1;
x_21 = l_Lean_Name_toString(x_9, x_20);
x_22 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_26);
return x_13;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
if (lean_obj_tag(x_27) == 6)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_3);
x_29 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_3);
x_30 = 1;
x_31 = l_Lean_Name_toString(x_9, x_30);
x_32 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_36);
return x_13;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
if (lean_obj_tag(x_37) == 6)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_1830_(x_28, x_38);
lean_dec(x_38);
lean_dec(x_28);
if (x_39 == 0)
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_10);
lean_dec(x_3);
x_40 = 1;
x_41 = l_Lean_Name_toString(x_9, x_40);
x_42 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_44 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_46);
return x_13;
}
else
{
lean_object* x_47; 
lean_free_object(x_13);
lean_dec(x_9);
x_47 = lean_box(0);
x_1 = x_10;
x_2 = x_47;
x_5 = x_16;
goto _start;
}
}
else
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_37);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_3);
x_49 = 1;
x_50 = l_Lean_Name_toString(x_9, x_49);
x_51 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_55);
return x_13;
}
}
}
else
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_3);
x_56 = 1;
x_57 = l_Lean_Name_toString(x_9, x_56);
x_58 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_62);
return x_13;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_13, 0);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_13);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
lean_inc(x_9);
x_67 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_66, x_9);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_10);
lean_dec(x_3);
x_68 = 1;
x_69 = l_Lean_Name_toString(x_9, x_68);
x_70 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_73 = lean_string_append(x_71, x_72);
x_74 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_64);
return x_75;
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
lean_dec(x_67);
if (lean_obj_tag(x_76) == 6)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_9);
lean_inc(x_3);
x_78 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_77);
lean_dec(x_10);
lean_dec(x_3);
x_79 = 1;
x_80 = l_Lean_Name_toString(x_9, x_79);
x_81 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_82 = lean_string_append(x_81, x_80);
lean_dec(x_80);
x_83 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_64);
return x_86;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_78, 0);
lean_inc(x_87);
lean_dec(x_78);
if (lean_obj_tag(x_87) == 6)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_1830_(x_77, x_88);
lean_dec(x_88);
lean_dec(x_77);
if (x_89 == 0)
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_10);
lean_dec(x_3);
x_90 = 1;
x_91 = l_Lean_Name_toString(x_9, x_90);
x_92 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__2;
x_93 = lean_string_append(x_92, x_91);
lean_dec(x_91);
x_94 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_95 = lean_string_append(x_93, x_94);
x_96 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_64);
return x_97;
}
else
{
lean_object* x_98; 
lean_dec(x_9);
x_98 = lean_box(0);
x_1 = x_10;
x_2 = x_98;
x_5 = x_64;
goto _start;
}
}
else
{
uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_87);
lean_dec(x_77);
lean_dec(x_10);
lean_dec(x_3);
x_100 = 1;
x_101 = l_Lean_Name_toString(x_9, x_100);
x_102 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_103 = lean_string_append(x_102, x_101);
lean_dec(x_101);
x_104 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_105 = lean_string_append(x_103, x_104);
x_106 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_64);
return x_107;
}
}
}
else
{
uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_76);
lean_dec(x_10);
lean_dec(x_3);
x_108 = 1;
x_109 = l_Lean_Name_toString(x_9, x_108);
x_110 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___closed__1;
x_111 = lean_string_append(x_110, x_109);
lean_dec(x_109);
x_112 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_113 = lean_string_append(x_111, x_112);
x_114 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_64);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_116 = !lean_is_exclusive(x_11);
if (x_116 == 0)
{
return x_11;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_11, 0);
x_118 = lean_ctor_get(x_11, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_11);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedConstructors___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_checkPostponedConstructors(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("No such recursor ", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Invalid recursor ", 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
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
lean_inc(x_3);
x_11 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_9);
x_19 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_18, x_9);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_3);
x_20 = 1;
x_21 = l_Lean_Name_toString(x_9, x_20);
x_22 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_26);
return x_13;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
if (lean_obj_tag(x_27) == 7)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_3);
x_29 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_3);
x_30 = 1;
x_31 = l_Lean_Name_toString(x_9, x_30);
x_32 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_36);
return x_13;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
if (lean_obj_tag(x_37) == 7)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_2226_(x_28, x_38);
lean_dec(x_38);
lean_dec(x_28);
if (x_39 == 0)
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_10);
lean_dec(x_3);
x_40 = 1;
x_41 = l_Lean_Name_toString(x_9, x_40);
x_42 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_44 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_46);
return x_13;
}
else
{
lean_object* x_47; 
lean_free_object(x_13);
lean_dec(x_9);
x_47 = lean_box(0);
x_1 = x_10;
x_2 = x_47;
x_5 = x_16;
goto _start;
}
}
else
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_37);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_3);
x_49 = 1;
x_50 = l_Lean_Name_toString(x_9, x_49);
x_51 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_55);
return x_13;
}
}
}
else
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_3);
x_56 = 1;
x_57 = l_Lean_Name_toString(x_9, x_56);
x_58 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_62);
return x_13;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_13, 0);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_13);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
lean_inc(x_9);
x_67 = l_Lean_SMap_find_x3f___at_Lean_Environment_Replay_checkPostponedConstructors___spec__1(x_66, x_9);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_10);
lean_dec(x_3);
x_68 = 1;
x_69 = l_Lean_Name_toString(x_9, x_68);
x_70 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_73 = lean_string_append(x_71, x_72);
x_74 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_64);
return x_75;
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
lean_dec(x_67);
if (lean_obj_tag(x_76) == 7)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_9);
lean_inc(x_3);
x_78 = l_Lean_HashMapImp_find_x3f___at_Lean_Environment_find_x3f___spec__5(x_3, x_9);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_77);
lean_dec(x_10);
lean_dec(x_3);
x_79 = 1;
x_80 = l_Lean_Name_toString(x_9, x_79);
x_81 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_82 = lean_string_append(x_81, x_80);
lean_dec(x_80);
x_83 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_64);
return x_86;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_78, 0);
lean_inc(x_87);
lean_dec(x_78);
if (lean_obj_tag(x_87) == 7)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_2226_(x_77, x_88);
lean_dec(x_88);
lean_dec(x_77);
if (x_89 == 0)
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_10);
lean_dec(x_3);
x_90 = 1;
x_91 = l_Lean_Name_toString(x_9, x_90);
x_92 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__2;
x_93 = lean_string_append(x_92, x_91);
lean_dec(x_91);
x_94 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_95 = lean_string_append(x_93, x_94);
x_96 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_64);
return x_97;
}
else
{
lean_object* x_98; 
lean_dec(x_9);
x_98 = lean_box(0);
x_1 = x_10;
x_2 = x_98;
x_5 = x_64;
goto _start;
}
}
else
{
uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_87);
lean_dec(x_77);
lean_dec(x_10);
lean_dec(x_3);
x_100 = 1;
x_101 = l_Lean_Name_toString(x_9, x_100);
x_102 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_103 = lean_string_append(x_102, x_101);
lean_dec(x_101);
x_104 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_105 = lean_string_append(x_103, x_104);
x_106 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_64);
return x_107;
}
}
}
else
{
uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_76);
lean_dec(x_10);
lean_dec(x_3);
x_108 = 1;
x_109 = l_Lean_Name_toString(x_9, x_108);
x_110 = l_Lean_RBNode_forIn_visit___at_Lean_Environment_Replay_checkPostponedRecursors___spec__1___closed__1;
x_111 = lean_string_append(x_110, x_109);
lean_dec(x_109);
x_112 = l_Lean_Environment_Replay_throwKernelException___closed__2;
x_113 = lean_string_append(x_111, x_112);
x_114 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_64);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_116 = !lean_is_exclusive(x_11);
if (x_116 == 0)
{
return x_11;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_11, 0);
x_118 = lean_ctor_get(x_11, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_11);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
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
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_checkPostponedRecursors(x_1, x_2, x_3);
lean_dec(x_2);
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
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_replay___spec__3(x_3, x_8, x_9, x_2);
lean_dec(x_3);
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
lean_inc(x_1);
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
lean_inc(x_1);
x_14 = l_Lean_Environment_Replay_checkPostponedConstructors(x_1, x_11, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Environment_Replay_checkPostponedRecursors(x_1, x_11, x_15);
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Replay(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
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
