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
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstant(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_addDeclCore(lean_object*, size_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Environment_Replay_checkPostponedConstructors___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Environment_Replay_replayConstant_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1___boxed(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Environment_Replay_replayConstant_spec__3___closed__0;
uint8_t l_Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3569_(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_replayConstant___closed__2;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replay(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0(uint8_t, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1(lean_object*, lean_object*);
uint8_t l_Lean_beqConstructorVal____x40_Lean_Declaration___hyg_3119_(lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_checkPostponedRecursors___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Environment_replay_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedConstantInfo;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_replayConstant___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1;
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstants(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__0;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_replayConstant___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_replayConstants_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Environment_Replay_replayConstant___closed__1;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Environment_replay_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
lean_object* l_Lean_RBNode_balLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__0;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = l_Lean_Name_quickCmp(x_1, x_5);
switch (x_8) {
case 0:
{
uint8_t x_9; 
x_9 = l_Lean_RBNode_isBlack___redArg(x_4);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_4);
lean_ctor_set(x_2, 0, x_11);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_10);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_2);
x_12 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_4);
x_13 = l_Lean_RBNode_balLeft___redArg(x_12, x_5, x_6, x_7);
return x_13;
}
}
case 1:
{
lean_object* x_14; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
x_14 = l_Lean_RBNode_appendTrees___redArg(x_4, x_7);
return x_14;
}
default: 
{
uint8_t x_15; 
x_15 = l_Lean_RBNode_isBlack___redArg(x_7);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
x_17 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_7);
lean_ctor_set(x_2, 3, x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_16);
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_2);
x_18 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_7);
x_19 = l_Lean_RBNode_balRight___redArg(x_4, x_5, x_6, x_18);
return x_19;
}
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_24 = l_Lean_Name_quickCmp(x_1, x_21);
switch (x_24) {
case 0:
{
uint8_t x_25; 
x_25 = l_Lean_RBNode_isBlack___redArg(x_20);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = 0;
x_27 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_20);
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_20);
x_30 = l_Lean_RBNode_balLeft___redArg(x_29, x_21, x_22, x_23);
return x_30;
}
}
case 1:
{
lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_21);
x_31 = l_Lean_RBNode_appendTrees___redArg(x_20, x_23);
return x_31;
}
default: 
{
uint8_t x_32; 
x_32 = l_Lean_RBNode_isBlack___redArg(x_23);
if (x_32 == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = 0;
x_34 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_23);
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_21);
lean_ctor_set(x_35, 2, x_22);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_23);
x_37 = l_Lean_RBNode_balRight___redArg(x_20, x_21, x_22, x_36);
return x_37;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_NameSet_contains(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_free_object(x_4);
x_11 = lean_st_ref_take(x_2, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 2);
x_17 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_1, x_15);
x_18 = l_Lean_NameSet_insert(x_16, x_1);
lean_ctor_set(x_12, 2, x_18);
lean_ctor_set(x_12, 1, x_17);
x_19 = lean_st_ref_set(x_2, x_12, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(x_9);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
x_28 = lean_ctor_get(x_12, 2);
x_29 = lean_ctor_get(x_12, 3);
x_30 = lean_ctor_get(x_12, 4);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_31 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_1, x_27);
x_32 = l_Lean_NameSet_insert(x_28, x_1);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_29);
lean_ctor_set(x_33, 4, x_30);
x_34 = lean_st_ref_set(x_2, x_33, x_13);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(x_9);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_4, 0);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_NameSet_contains(x_41, x_1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_45 = lean_st_ref_take(x_2, x_40);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 4);
lean_inc(x_52);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 lean_ctor_release(x_46, 4);
 x_53 = x_46;
} else {
 lean_dec_ref(x_46);
 x_53 = lean_box(0);
}
x_54 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_1, x_49);
x_55 = l_Lean_NameSet_insert(x_50, x_1);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 5, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_51);
lean_ctor_set(x_56, 4, x_52);
x_57 = lean_st_ref_set(x_2, x_56, x_47);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(x_42);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_isTodo___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_isTodo___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_box(0);
x_4 = l_Lean_Kernel_Exception_toMessageData(x_1, x_3);
x_5 = l_Lean_MessageData_toString(x_4, x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_throwKernelException___redArg(x_1, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = 0;
x_9 = lean_box(0);
x_10 = 1;
x_11 = l_Lean_Environment_addDeclCore(x_7, x_8, x_1, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Environment_Replay_throwKernelException___redArg(x_12, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_st_ref_take(x_2, x_6);
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
x_20 = lean_st_ref_set(x_2, x_16, x_17);
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
x_32 = lean_st_ref_set(x_2, x_31, x_17);
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
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_addDecl___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_addDecl___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_addDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_List_reverse___redArg(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_3, 1);
x_11 = l_Lean_instInhabitedConstantInfo;
x_12 = lean_array_get_size(x_10);
x_13 = l_Lean_Name_hash___override(x_8);
x_14 = 32;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = 16;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = 1;
x_23 = lean_usize_sub(x_21, x_22);
x_24 = lean_usize_land(x_20, x_23);
x_25 = lean_array_uget(x_10, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(x_11, x_8, x_25);
lean_dec(x_25);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_26);
{
lean_object* _tmp_0 = x_9;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; size_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_30 = lean_ctor_get(x_3, 1);
x_31 = l_Lean_instInhabitedConstantInfo;
x_32 = lean_array_get_size(x_30);
x_33 = l_Lean_Name_hash___override(x_28);
x_34 = 32;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = 16;
x_38 = lean_uint64_shift_right(x_36, x_37);
x_39 = lean_uint64_xor(x_36, x_38);
x_40 = lean_uint64_to_usize(x_39);
x_41 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_42 = 1;
x_43 = lean_usize_sub(x_41, x_42);
x_44 = lean_usize_land(x_40, x_43);
x_45 = lean_array_uget(x_30, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(x_31, x_28, x_45);
lean_dec(x_45);
lean_dec(x_28);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_2);
x_1 = x_29;
x_2 = x_47;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_List_reverse___redArg(x_2);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_3, 1);
x_12 = l_Lean_instInhabitedConstantInfo;
x_13 = lean_array_get_size(x_11);
x_14 = l_Lean_Name_hash___override(x_9);
x_15 = 32;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = 16;
x_19 = lean_uint64_shift_right(x_17, x_18);
x_20 = lean_uint64_xor(x_17, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_23 = 1;
x_24 = lean_usize_sub(x_22, x_23);
x_25 = lean_usize_land(x_21, x_24);
x_26 = lean_array_uget(x_11, x_25);
x_27 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(x_12, x_9, x_26);
lean_dec(x_26);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_27);
x_28 = l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg(x_10, x_1, x_3, x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_31 = lean_ctor_get(x_3, 1);
x_32 = l_Lean_instInhabitedConstantInfo;
x_33 = lean_array_get_size(x_31);
x_34 = l_Lean_Name_hash___override(x_29);
x_35 = 32;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = 16;
x_39 = lean_uint64_shift_right(x_37, x_38);
x_40 = lean_uint64_xor(x_37, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_43 = 1;
x_44 = lean_usize_sub(x_42, x_43);
x_45 = lean_usize_land(x_41, x_44);
x_46 = lean_array_uget(x_31, x_45);
x_47 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(x_32, x_29, x_46);
lean_dec(x_46);
lean_dec(x_29);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_2);
x_49 = l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg(x_30, x_48, x_3, x_5);
return x_49;
}
}
}
}
static lean_object* _init_l_panic___at___Lean_Environment_Replay_replayConstant_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Environment_Replay_replayConstant_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_panic___at___Lean_Environment_Replay_replayConstant_spec__3___closed__0;
x_6 = l_ReaderT_instMonad___redArg(x_5);
x_7 = lean_box(0);
x_8 = l_instInhabitedOfMonad___redArg(x_6, x_7);
x_9 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_3(x_10, x_2, x_3, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_ConstantInfo_getUsedConstantsAsSet(x_8);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Environment_Replay_replayConstants(x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
{
lean_object* _tmp_1 = x_9;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_5 = x_12;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4___redArg(x_1, x_3, x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_st_ref_take(x_4, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 2);
x_15 = l_Lean_ConstantInfo_name(x_7);
x_16 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_15, x_13);
x_17 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_15, x_14);
lean_dec(x_15);
lean_ctor_set(x_10, 2, x_17);
lean_ctor_set(x_10, 1, x_16);
x_18 = lean_st_ref_set(x_4, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_4 = x_19;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
x_23 = lean_ctor_get(x_10, 2);
x_24 = lean_ctor_get(x_10, 3);
x_25 = lean_ctor_get(x_10, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_26 = l_Lean_ConstantInfo_name(x_7);
x_27 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_26, x_22);
x_28 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_26, x_23);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set(x_29, 4, x_25);
x_30 = lean_st_ref_set(x_4, x_29, x_11);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_4 = x_31;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_5 = _tmp_4;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg(x_1, x_3, x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_st_ref_take(x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 2);
x_17 = l_Lean_ConstantInfo_name(x_9);
x_18 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_17, x_15);
x_19 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_17, x_16);
lean_dec(x_17);
lean_ctor_set(x_12, 2, x_19);
lean_ctor_set(x_12, 1, x_18);
x_20 = lean_st_ref_set(x_6, x_12, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg(x_1, x_10, x_1, x_6, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
x_26 = lean_ctor_get(x_12, 3);
x_27 = lean_ctor_get(x_12, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_28 = l_Lean_ConstantInfo_name(x_9);
x_29 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_28, x_24);
x_30 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_28, x_25);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_27);
x_32 = lean_st_ref_set(x_6, x_31, x_13);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg(x_1, x_10, x_1, x_6, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_List_reverse___redArg(x_2);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lean_ConstantInfo_inductiveVal_x21(x_9);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(x_12, x_13, x_3, x_4, x_5);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_ctor_set(x_14, 1, x_16);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_10;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_4 = x_17;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_5 = _tmp_4;
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
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_21);
{
lean_object* _tmp_0 = x_10;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_4 = x_20;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_5 = _tmp_4;
}
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = l_Lean_ConstantInfo_inductiveVal_x21(x_23);
x_26 = lean_ctor_get(x_25, 4);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(x_26, x_27, x_3, x_4, x_5);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_2);
x_1 = x_24;
x_2 = x_33;
x_5 = x_30;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4___redArg(x_1, x_10, x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
{
lean_object* _tmp_1 = x_9;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_5 = x_12;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___redArg(x_1, x_3, x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
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
x_12 = l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__0(x_8, x_11);
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
x_22 = l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__0(x_18, x_21);
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
static lean_object* _init_l_Lean_Environment_Replay_replayConstant___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Replay", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_replayConstant___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Environment.Replay.replayConstant", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_replayConstant___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Environment_Replay_replayConstant___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Environment_Replay_replayConstant___closed__2;
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_unsigned_to_nat(74u);
x_4 = l_Lean_Environment_Replay_replayConstant___closed__1;
x_5 = l_Lean_Environment_Replay_replayConstant___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_inc(x_1);
x_33 = l_Lean_Environment_Replay_isTodo___redArg(x_1, x_3, x_4);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; size_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
x_44 = lean_array_get_size(x_43);
x_45 = l_Lean_Name_hash___override(x_1);
x_46 = 32;
x_47 = lean_uint64_shift_right(x_45, x_46);
x_48 = lean_uint64_xor(x_45, x_47);
x_49 = 16;
x_50 = lean_uint64_shift_right(x_48, x_49);
x_51 = lean_uint64_xor(x_48, x_50);
x_52 = lean_uint64_to_usize(x_51);
x_53 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_54 = 1;
x_55 = lean_usize_sub(x_53, x_54);
x_56 = lean_usize_land(x_52, x_55);
x_57 = lean_array_uget(x_43, x_56);
lean_dec(x_43);
x_58 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_1, x_57);
lean_dec(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_1);
x_59 = l_Lean_Environment_Replay_replayConstant___closed__3;
x_60 = l_panic___at___Lean_Environment_Replay_replayConstant_spec__3(x_59, x_2, x_3, x_42);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
lean_inc(x_61);
x_62 = l_Lean_ConstantInfo_getUsedConstantsAsSet(x_61);
lean_inc(x_3);
lean_inc(x_2);
x_63 = l_Lean_Environment_Replay_replayConstants(x_62, x_2, x_3, x_42);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_get(x_3, x_64);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
x_69 = lean_ctor_get(x_67, 2);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_NameSet_contains(x_69, x_1);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_61);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_box(0);
lean_ctor_set(x_65, 0, x_71);
return x_65;
}
else
{
lean_free_object(x_65);
switch (lean_obj_tag(x_61)) {
case 0:
{
uint8_t x_72; 
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_61);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_Lean_Environment_Replay_addDecl___redArg(x_61, x_3, x_68);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_5 = x_3;
x_6 = x_74;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_73;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_61, 0);
lean_inc(x_75);
lean_dec(x_61);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_Environment_Replay_addDecl___redArg(x_76, x_3, x_68);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_5 = x_3;
x_6 = x_78;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_77;
}
}
}
case 1:
{
uint8_t x_79; 
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_61);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = l_Lean_Environment_Replay_addDecl___redArg(x_61, x_3, x_68);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_5 = x_3;
x_6 = x_81;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_80;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_61, 0);
lean_inc(x_82);
lean_dec(x_61);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_Environment_Replay_addDecl___redArg(x_83, x_3, x_68);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_5 = x_3;
x_6 = x_85;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_84;
}
}
}
case 2:
{
uint8_t x_86; 
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_61);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = l_Lean_Environment_Replay_addDecl___redArg(x_61, x_3, x_68);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_5 = x_3;
x_6 = x_88;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_87;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_61, 0);
lean_inc(x_89);
lean_dec(x_61);
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Lean_Environment_Replay_addDecl___redArg(x_90, x_3, x_68);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_5 = x_3;
x_6 = x_92;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_91;
}
}
}
case 3:
{
uint8_t x_93; 
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_61);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = l_Lean_Environment_Replay_addDecl___redArg(x_61, x_3, x_68);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_5 = x_3;
x_6 = x_95;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_94;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_61, 0);
lean_inc(x_96);
lean_dec(x_61);
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l_Lean_Environment_Replay_addDecl___redArg(x_97, x_3, x_68);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_5 = x_3;
x_6 = x_99;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_98;
}
}
}
case 4:
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_61);
lean_dec(x_2);
x_100 = lean_box(4);
x_101 = l_Lean_Environment_Replay_addDecl___redArg(x_100, x_3, x_68);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_5 = x_3;
x_6 = x_102;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_101;
}
}
case 5:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_103 = lean_ctor_get(x_61, 0);
lean_inc(x_103);
lean_dec(x_61);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 3);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_box(0);
x_108 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(x_106, x_107, x_2, x_3, x_68);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_box(0);
x_112 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg(x_111, x_109, x_109, x_111, x_2, x_3, x_110);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_box(0);
x_115 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7(x_109, x_114, x_2, x_3, x_113);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
lean_inc(x_3);
lean_inc(x_116);
x_118 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___redArg(x_111, x_116, x_111, x_2, x_3, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_ctor_get(x_104, 1);
lean_inc(x_120);
lean_dec(x_104);
x_121 = lean_box(0);
x_122 = l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__9(x_116, x_121);
x_123 = 0;
x_124 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_105);
lean_ctor_set(x_124, 2, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*3, x_123);
x_125 = l_Lean_Environment_Replay_addDecl___redArg(x_124, x_3, x_119);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_5 = x_3;
x_6 = x_126;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_125;
}
}
else
{
lean_dec(x_116);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_3);
lean_dec(x_1);
return x_118;
}
}
case 6:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_2);
x_127 = lean_ctor_get(x_61, 0);
lean_inc(x_127);
lean_dec(x_61);
x_128 = lean_st_ref_take(x_3, x_68);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = !lean_is_exclusive(x_129);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_129, 3);
x_134 = lean_ctor_get(x_130, 0);
lean_inc(x_134);
lean_dec(x_130);
x_135 = l_Lean_NameSet_insert(x_133, x_134);
lean_ctor_set(x_129, 3, x_135);
x_136 = lean_st_ref_set(x_3, x_129, x_131);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_5 = x_3;
x_6 = x_137;
goto block_32;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_138 = lean_ctor_get(x_129, 0);
x_139 = lean_ctor_get(x_129, 1);
x_140 = lean_ctor_get(x_129, 2);
x_141 = lean_ctor_get(x_129, 3);
x_142 = lean_ctor_get(x_129, 4);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_129);
x_143 = lean_ctor_get(x_130, 0);
lean_inc(x_143);
lean_dec(x_130);
x_144 = l_Lean_NameSet_insert(x_141, x_143);
x_145 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_145, 0, x_138);
lean_ctor_set(x_145, 1, x_139);
lean_ctor_set(x_145, 2, x_140);
lean_ctor_set(x_145, 3, x_144);
lean_ctor_set(x_145, 4, x_142);
x_146 = lean_st_ref_set(x_3, x_145, x_131);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_5 = x_3;
x_6 = x_147;
goto block_32;
}
}
default: 
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_dec(x_2);
x_148 = lean_ctor_get(x_61, 0);
lean_inc(x_148);
lean_dec(x_61);
x_149 = lean_st_ref_take(x_3, x_68);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
lean_dec(x_148);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = !lean_is_exclusive(x_150);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_150, 4);
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
lean_dec(x_151);
x_156 = l_Lean_NameSet_insert(x_154, x_155);
lean_ctor_set(x_150, 4, x_156);
x_157 = lean_st_ref_set(x_3, x_150, x_152);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_5 = x_3;
x_6 = x_158;
goto block_32;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_159 = lean_ctor_get(x_150, 0);
x_160 = lean_ctor_get(x_150, 1);
x_161 = lean_ctor_get(x_150, 2);
x_162 = lean_ctor_get(x_150, 3);
x_163 = lean_ctor_get(x_150, 4);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_150);
x_164 = lean_ctor_get(x_151, 0);
lean_inc(x_164);
lean_dec(x_151);
x_165 = l_Lean_NameSet_insert(x_163, x_164);
x_166 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_166, 0, x_159);
lean_ctor_set(x_166, 1, x_160);
lean_ctor_set(x_166, 2, x_161);
lean_ctor_set(x_166, 3, x_162);
lean_ctor_set(x_166, 4, x_165);
x_167 = lean_st_ref_set(x_3, x_166, x_152);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_5 = x_3;
x_6 = x_168;
goto block_32;
}
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_169 = lean_ctor_get(x_65, 0);
x_170 = lean_ctor_get(x_65, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_65);
x_171 = lean_ctor_get(x_169, 2);
lean_inc(x_171);
lean_dec(x_169);
x_172 = l_Lean_NameSet_contains(x_171, x_1);
lean_dec(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_61);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_box(0);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_170);
return x_174;
}
else
{
switch (lean_obj_tag(x_61)) {
case 0:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_2);
x_175 = lean_ctor_get(x_61, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_176 = x_61;
} else {
 lean_dec_ref(x_61);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 1, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_175);
x_178 = l_Lean_Environment_Replay_addDecl___redArg(x_177, x_3, x_170);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_5 = x_3;
x_6 = x_179;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_178;
}
}
case 1:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_2);
x_180 = lean_ctor_get(x_61, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_181 = x_61;
} else {
 lean_dec_ref(x_61);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_180);
x_183 = l_Lean_Environment_Replay_addDecl___redArg(x_182, x_3, x_170);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_5 = x_3;
x_6 = x_184;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_183;
}
}
case 2:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_2);
x_185 = lean_ctor_get(x_61, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_186 = x_61;
} else {
 lean_dec_ref(x_61);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(2, 1, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_185);
x_188 = l_Lean_Environment_Replay_addDecl___redArg(x_187, x_3, x_170);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_5 = x_3;
x_6 = x_189;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_188;
}
}
case 3:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_2);
x_190 = lean_ctor_get(x_61, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_191 = x_61;
} else {
 lean_dec_ref(x_61);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(3, 1, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_190);
x_193 = l_Lean_Environment_Replay_addDecl___redArg(x_192, x_3, x_170);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_5 = x_3;
x_6 = x_194;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_193;
}
}
case 4:
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_61);
lean_dec(x_2);
x_195 = lean_box(4);
x_196 = l_Lean_Environment_Replay_addDecl___redArg(x_195, x_3, x_170);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_5 = x_3;
x_6 = x_197;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_196;
}
}
case 5:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_198 = lean_ctor_get(x_61, 0);
lean_inc(x_198);
lean_dec(x_61);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 3);
lean_inc(x_201);
lean_dec(x_198);
x_202 = lean_box(0);
x_203 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(x_201, x_202, x_2, x_3, x_170);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_box(0);
x_207 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg(x_206, x_204, x_204, x_206, x_2, x_3, x_205);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_box(0);
x_210 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7(x_204, x_209, x_2, x_3, x_208);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
lean_inc(x_3);
lean_inc(x_211);
x_213 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___redArg(x_206, x_211, x_206, x_2, x_3, x_212);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; 
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_215 = lean_ctor_get(x_199, 1);
lean_inc(x_215);
lean_dec(x_199);
x_216 = lean_box(0);
x_217 = l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__9(x_211, x_216);
x_218 = 0;
x_219 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_219, 0, x_215);
lean_ctor_set(x_219, 1, x_200);
lean_ctor_set(x_219, 2, x_217);
lean_ctor_set_uint8(x_219, sizeof(void*)*3, x_218);
x_220 = l_Lean_Environment_Replay_addDecl___redArg(x_219, x_3, x_214);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_5 = x_3;
x_6 = x_221;
goto block_32;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_220;
}
}
else
{
lean_dec(x_211);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_3);
lean_dec(x_1);
return x_213;
}
}
case 6:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_2);
x_222 = lean_ctor_get(x_61, 0);
lean_inc(x_222);
lean_dec(x_61);
x_223 = lean_st_ref_take(x_3, x_170);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
lean_dec(x_223);
x_227 = lean_ctor_get(x_224, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_224, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_224, 3);
lean_inc(x_230);
x_231 = lean_ctor_get(x_224, 4);
lean_inc(x_231);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 lean_ctor_release(x_224, 2);
 lean_ctor_release(x_224, 3);
 lean_ctor_release(x_224, 4);
 x_232 = x_224;
} else {
 lean_dec_ref(x_224);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_225, 0);
lean_inc(x_233);
lean_dec(x_225);
x_234 = l_Lean_NameSet_insert(x_230, x_233);
if (lean_is_scalar(x_232)) {
 x_235 = lean_alloc_ctor(0, 5, 0);
} else {
 x_235 = x_232;
}
lean_ctor_set(x_235, 0, x_227);
lean_ctor_set(x_235, 1, x_228);
lean_ctor_set(x_235, 2, x_229);
lean_ctor_set(x_235, 3, x_234);
lean_ctor_set(x_235, 4, x_231);
x_236 = lean_st_ref_set(x_3, x_235, x_226);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
x_5 = x_3;
x_6 = x_237;
goto block_32;
}
default: 
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_2);
x_238 = lean_ctor_get(x_61, 0);
lean_inc(x_238);
lean_dec(x_61);
x_239 = lean_st_ref_take(x_3, x_170);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_238, 0);
lean_inc(x_241);
lean_dec(x_238);
x_242 = lean_ctor_get(x_239, 1);
lean_inc(x_242);
lean_dec(x_239);
x_243 = lean_ctor_get(x_240, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_240, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_240, 2);
lean_inc(x_245);
x_246 = lean_ctor_get(x_240, 3);
lean_inc(x_246);
x_247 = lean_ctor_get(x_240, 4);
lean_inc(x_247);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 lean_ctor_release(x_240, 3);
 lean_ctor_release(x_240, 4);
 x_248 = x_240;
} else {
 lean_dec_ref(x_240);
 x_248 = lean_box(0);
}
x_249 = lean_ctor_get(x_241, 0);
lean_inc(x_249);
lean_dec(x_241);
x_250 = l_Lean_NameSet_insert(x_247, x_249);
if (lean_is_scalar(x_248)) {
 x_251 = lean_alloc_ctor(0, 5, 0);
} else {
 x_251 = x_248;
}
lean_ctor_set(x_251, 0, x_243);
lean_ctor_set(x_251, 1, x_244);
lean_ctor_set(x_251, 2, x_245);
lean_ctor_set(x_251, 3, x_246);
lean_ctor_set(x_251, 4, x_250);
x_252 = lean_st_ref_set(x_3, x_251, x_242);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_5 = x_3;
x_6 = x_253;
goto block_32;
}
}
}
}
}
else
{
lean_dec(x_61);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_63;
}
}
}
block_32:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 2);
x_12 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_1, x_11);
lean_dec(x_1);
lean_ctor_set(x_8, 2, x_12);
x_13 = lean_st_ref_set(x_5, x_8, x_9);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_25 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_1, x_22);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_24);
x_27 = lean_st_ref_set(x_5, x_26, x_9);
lean_dec(x_5);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_replayConstants_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_replayConstants_spec__0(x_1, x_9, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Environment_Replay_replayConstant(x_10, x_4, x_5, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
{
lean_object* _tmp_1 = x_11;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_5 = x_16;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_6 = _tmp_5;
}
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstants(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_replayConstants_spec__0(x_5, x_1, x_5, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("No such constructor ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid constructor ", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_21; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_1);
x_21 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_6, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 0;
lean_inc(x_11);
x_29 = l_Lean_Environment_find_x3f(x_27, x_11, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_free_object(x_23);
lean_dec(x_12);
x_13 = x_26;
goto block_20;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 6)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_5, 1);
x_33 = lean_array_get_size(x_32);
x_34 = l_Lean_Name_hash___override(x_11);
x_35 = 32;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = 16;
x_39 = lean_uint64_shift_right(x_37, x_38);
x_40 = lean_uint64_xor(x_37, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_43 = 1;
x_44 = lean_usize_sub(x_42, x_43);
x_45 = lean_usize_land(x_41, x_44);
x_46 = lean_array_uget(x_32, x_45);
x_47 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_11, x_46);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_dec(x_31);
lean_free_object(x_23);
lean_dec(x_12);
x_13 = x_26;
goto block_20;
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 6)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = l_Lean_beqConstructorVal____x40_Lean_Declaration___hyg_3119_(x_31, x_50);
lean_dec(x_50);
lean_dec(x_31);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_12);
lean_dec(x_1);
x_52 = lean_box(x_51);
x_53 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = 1;
x_55 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1;
x_56 = l_Lean_Name_toString(x_11, x_54, x_53);
x_57 = lean_string_append(x_55, x_56);
lean_dec(x_56);
lean_ctor_set_tag(x_48, 18);
lean_ctor_set(x_48, 0, x_57);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_48);
return x_23;
}
else
{
lean_free_object(x_48);
lean_free_object(x_23);
lean_dec(x_11);
{
lean_object* _tmp_2 = x_12;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_6 = x_26;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_48, 0);
lean_inc(x_59);
lean_dec(x_48);
x_60 = l_Lean_beqConstructorVal____x40_Lean_Declaration___hyg_3119_(x_31, x_59);
lean_dec(x_59);
lean_dec(x_31);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_12);
lean_dec(x_1);
x_61 = lean_box(x_60);
x_62 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_62, 0, x_61);
x_63 = 1;
x_64 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1;
x_65 = l_Lean_Name_toString(x_11, x_63, x_62);
x_66 = lean_string_append(x_64, x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_67);
return x_23;
}
else
{
lean_free_object(x_23);
lean_dec(x_11);
{
lean_object* _tmp_2 = x_12;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_6 = x_26;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_31);
lean_free_object(x_23);
lean_dec(x_12);
x_13 = x_26;
goto block_20;
}
}
}
else
{
lean_dec(x_30);
lean_free_object(x_23);
lean_dec(x_12);
x_13 = x_26;
goto block_20;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_23, 0);
x_70 = lean_ctor_get(x_23, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_23);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = 0;
lean_inc(x_11);
x_73 = l_Lean_Environment_find_x3f(x_71, x_11, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_dec(x_12);
x_13 = x_70;
goto block_20;
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 6)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; size_t x_85; size_t x_86; size_t x_87; size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_ctor_get(x_5, 1);
x_77 = lean_array_get_size(x_76);
x_78 = l_Lean_Name_hash___override(x_11);
x_79 = 32;
x_80 = lean_uint64_shift_right(x_78, x_79);
x_81 = lean_uint64_xor(x_78, x_80);
x_82 = 16;
x_83 = lean_uint64_shift_right(x_81, x_82);
x_84 = lean_uint64_xor(x_81, x_83);
x_85 = lean_uint64_to_usize(x_84);
x_86 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_87 = 1;
x_88 = lean_usize_sub(x_86, x_87);
x_89 = lean_usize_land(x_85, x_88);
x_90 = lean_array_uget(x_76, x_89);
x_91 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_11, x_90);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_dec(x_75);
lean_dec(x_12);
x_13 = x_70;
goto block_20;
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec(x_91);
if (lean_obj_tag(x_92) == 6)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = l_Lean_beqConstructorVal____x40_Lean_Declaration___hyg_3119_(x_75, x_93);
lean_dec(x_93);
lean_dec(x_75);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_12);
lean_dec(x_1);
x_96 = lean_box(x_95);
x_97 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_97, 0, x_96);
x_98 = 1;
x_99 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1;
x_100 = l_Lean_Name_toString(x_11, x_98, x_97);
x_101 = lean_string_append(x_99, x_100);
lean_dec(x_100);
if (lean_is_scalar(x_94)) {
 x_102 = lean_alloc_ctor(18, 1, 0);
} else {
 x_102 = x_94;
 lean_ctor_set_tag(x_102, 18);
}
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_70);
return x_103;
}
else
{
lean_dec(x_94);
lean_dec(x_11);
{
lean_object* _tmp_2 = x_12;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_6 = x_70;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
}
else
{
lean_dec(x_92);
lean_dec(x_75);
lean_dec(x_12);
x_13 = x_70;
goto block_20;
}
}
}
else
{
lean_dec(x_74);
lean_dec(x_12);
x_13 = x_70;
goto block_20;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
return x_21;
}
block_20:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__0;
x_15 = 1;
x_16 = l_Lean_Name_toString(x_11, x_15, x_1);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_Replay_checkPostponedConstructors___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 3);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Environment_Replay_checkPostponedConstructors___lam__0___boxed), 1, 0);
x_9 = lean_box(0);
x_10 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0(x_8, x_9, x_7, x_9, x_1, x_2, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Environment_Replay_checkPostponedConstructors___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
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
static lean_object* _init_l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("No such recursor ", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid recursor ", 17, 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_21; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_1);
x_21 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_6, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 0;
lean_inc(x_11);
x_29 = l_Lean_Environment_find_x3f(x_27, x_11, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_free_object(x_23);
lean_dec(x_12);
x_13 = x_26;
goto block_20;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 7)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_5, 1);
x_33 = lean_array_get_size(x_32);
x_34 = l_Lean_Name_hash___override(x_11);
x_35 = 32;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = 16;
x_39 = lean_uint64_shift_right(x_37, x_38);
x_40 = lean_uint64_xor(x_37, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_43 = 1;
x_44 = lean_usize_sub(x_42, x_43);
x_45 = lean_usize_land(x_41, x_44);
x_46 = lean_array_uget(x_32, x_45);
x_47 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_11, x_46);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_dec(x_31);
lean_free_object(x_23);
lean_dec(x_12);
x_13 = x_26;
goto block_20;
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 7)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = l_Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3569_(x_31, x_50);
lean_dec(x_50);
lean_dec(x_31);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_12);
lean_dec(x_1);
x_52 = lean_box(x_51);
x_53 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = 1;
x_55 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1;
x_56 = l_Lean_Name_toString(x_11, x_54, x_53);
x_57 = lean_string_append(x_55, x_56);
lean_dec(x_56);
lean_ctor_set_tag(x_48, 18);
lean_ctor_set(x_48, 0, x_57);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_48);
return x_23;
}
else
{
lean_free_object(x_48);
lean_free_object(x_23);
lean_dec(x_11);
{
lean_object* _tmp_2 = x_12;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_6 = x_26;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_48, 0);
lean_inc(x_59);
lean_dec(x_48);
x_60 = l_Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3569_(x_31, x_59);
lean_dec(x_59);
lean_dec(x_31);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_12);
lean_dec(x_1);
x_61 = lean_box(x_60);
x_62 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_62, 0, x_61);
x_63 = 1;
x_64 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1;
x_65 = l_Lean_Name_toString(x_11, x_63, x_62);
x_66 = lean_string_append(x_64, x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_67);
return x_23;
}
else
{
lean_free_object(x_23);
lean_dec(x_11);
{
lean_object* _tmp_2 = x_12;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_6 = x_26;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_31);
lean_free_object(x_23);
lean_dec(x_12);
x_13 = x_26;
goto block_20;
}
}
}
else
{
lean_dec(x_30);
lean_free_object(x_23);
lean_dec(x_12);
x_13 = x_26;
goto block_20;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_23, 0);
x_70 = lean_ctor_get(x_23, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_23);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = 0;
lean_inc(x_11);
x_73 = l_Lean_Environment_find_x3f(x_71, x_11, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_dec(x_12);
x_13 = x_70;
goto block_20;
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 7)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; size_t x_85; size_t x_86; size_t x_87; size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_ctor_get(x_5, 1);
x_77 = lean_array_get_size(x_76);
x_78 = l_Lean_Name_hash___override(x_11);
x_79 = 32;
x_80 = lean_uint64_shift_right(x_78, x_79);
x_81 = lean_uint64_xor(x_78, x_80);
x_82 = 16;
x_83 = lean_uint64_shift_right(x_81, x_82);
x_84 = lean_uint64_xor(x_81, x_83);
x_85 = lean_uint64_to_usize(x_84);
x_86 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_87 = 1;
x_88 = lean_usize_sub(x_86, x_87);
x_89 = lean_usize_land(x_85, x_88);
x_90 = lean_array_uget(x_76, x_89);
x_91 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_11, x_90);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_dec(x_75);
lean_dec(x_12);
x_13 = x_70;
goto block_20;
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec(x_91);
if (lean_obj_tag(x_92) == 7)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = l_Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3569_(x_75, x_93);
lean_dec(x_93);
lean_dec(x_75);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_12);
lean_dec(x_1);
x_96 = lean_box(x_95);
x_97 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_97, 0, x_96);
x_98 = 1;
x_99 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1;
x_100 = l_Lean_Name_toString(x_11, x_98, x_97);
x_101 = lean_string_append(x_99, x_100);
lean_dec(x_100);
if (lean_is_scalar(x_94)) {
 x_102 = lean_alloc_ctor(18, 1, 0);
} else {
 x_102 = x_94;
 lean_ctor_set_tag(x_102, 18);
}
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_70);
return x_103;
}
else
{
lean_dec(x_94);
lean_dec(x_11);
{
lean_object* _tmp_2 = x_12;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_6 = x_70;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
}
else
{
lean_dec(x_92);
lean_dec(x_75);
lean_dec(x_12);
x_13 = x_70;
goto block_20;
}
}
}
else
{
lean_dec(x_74);
lean_dec(x_12);
x_13 = x_70;
goto block_20;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
return x_21;
}
block_20:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__0;
x_15 = 1;
x_16 = l_Lean_Name_toString(x_11, x_15, x_1);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Environment_Replay_checkPostponedRecursors___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Environment_Replay_checkPostponedConstructors___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 4);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Environment_Replay_checkPostponedRecursors___closed__0;
x_9 = lean_box(0);
x_10 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0(x_8, x_9, x_7, x_9, x_1, x_2, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_11; 
x_11 = l_Lean_NameSet_insert(x_2, x_7);
x_1 = x_6;
x_2 = x_11;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0___redArg(x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1(x_1, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Environment_replay_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1(x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
x_2 = x_7;
x_4 = x_9;
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
lean_object* x_4; lean_object* x_5; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_box(0);
x_41 = lean_box(0);
x_42 = lean_array_get_size(x_20);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_42);
if (x_44 == 0)
{
lean_dec(x_42);
lean_dec(x_20);
x_22 = x_41;
goto block_40;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_46 = 0;
x_47 = l_Array_foldrMUnsafe_fold___at___Lean_Environment_replay_spec__2(x_20, x_45, x_46, x_41);
lean_dec(x_20);
x_22 = x_47;
goto block_40;
}
block_19:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_get(x_4, x_6);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
block_40:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0___redArg(x_22, x_21, x_3);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set(x_26, 4, x_21);
x_27 = lean_st_mk_ref(x_26, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
lean_inc(x_28);
lean_inc(x_1);
x_31 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_replayConstants_spec__0(x_30, x_24, x_30, x_1, x_28, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Environment_Replay_checkPostponedConstructors(x_1, x_28, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Environment_Replay_checkPostponedRecursors(x_1, x_28, x_34);
lean_dec(x_1);
x_4 = x_28;
x_5 = x_35;
goto block_19;
}
else
{
lean_dec(x_1);
x_4 = x_28;
x_5 = x_33;
goto block_19;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Environment_replay_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_Environment_replay_spec__2(x_1, x_5, x_6, x_4);
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
l_panic___at___Lean_Environment_Replay_replayConstant_spec__3___closed__0 = _init_l_panic___at___Lean_Environment_Replay_replayConstant_spec__3___closed__0();
lean_mark_persistent(l_panic___at___Lean_Environment_Replay_replayConstant_spec__3___closed__0);
l_Lean_Environment_Replay_replayConstant___closed__0 = _init_l_Lean_Environment_Replay_replayConstant___closed__0();
lean_mark_persistent(l_Lean_Environment_Replay_replayConstant___closed__0);
l_Lean_Environment_Replay_replayConstant___closed__1 = _init_l_Lean_Environment_Replay_replayConstant___closed__1();
lean_mark_persistent(l_Lean_Environment_Replay_replayConstant___closed__1);
l_Lean_Environment_Replay_replayConstant___closed__2 = _init_l_Lean_Environment_Replay_replayConstant___closed__2();
lean_mark_persistent(l_Lean_Environment_Replay_replayConstant___closed__2);
l_Lean_Environment_Replay_replayConstant___closed__3 = _init_l_Lean_Environment_Replay_replayConstant___closed__3();
lean_mark_persistent(l_Lean_Environment_Replay_replayConstant___closed__3);
l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__0 = _init_l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__0();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__0);
l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1 = _init_l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___closed__1);
l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__0 = _init_l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__0();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__0);
l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1 = _init_l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___closed__1);
l_Lean_Environment_Replay_checkPostponedRecursors___closed__0 = _init_l_Lean_Environment_Replay_checkPostponedRecursors___closed__0();
lean_mark_persistent(l_Lean_Environment_Replay_checkPostponedRecursors___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
