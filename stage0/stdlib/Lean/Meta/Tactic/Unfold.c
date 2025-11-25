// Lean compiler output
// Module: Lean.Meta.Tactic.Unfold
// Imports: public import Lean.Meta.Tactic.Delta public import Lean.Meta.Tactic.Simp.Main
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
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0;
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0;
static lean_object* l_Lean_Meta_unfoldTarget___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfold___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
static lean_object* l_Lean_Meta_unfoldTarget___lam__0___closed__1;
static lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0___closed__0;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfold___closed__7;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfoldTarget___lam__0___closed__0;
static lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0;
static lean_object* l_Lean_Meta_unfold___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_unfold___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isRflTheorem(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfold___closed__5;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfold___closed__2;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfold___lam__1___closed__0;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfoldTarget___lam__0___closed__3;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l_Lean_Meta_unfold___closed__4;
static lean_object* l_Lean_Meta_unfold___closed__3;
lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfold___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3;
lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_neutralConfig;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getSimpCongrTheorems___redArg(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0;
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 1;
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 22, x_8);
x_9 = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__1;
x_10 = l_Lean_Meta_Simp_mkContext___redArg(x_6, x_9, x_5, x_1, x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 1);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 2);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 3);
x_17 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 4);
x_18 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 5);
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 6);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 7);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 8);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 9);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 10);
x_24 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 11);
x_25 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 12);
x_26 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 13);
x_27 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 14);
x_28 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 15);
x_29 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 16);
x_30 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 17);
x_31 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 18);
x_32 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 19);
x_33 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 20);
x_34 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 21);
x_35 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 23);
x_36 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 24);
x_37 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 25);
x_38 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 26);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_39 = 1;
x_40 = lean_alloc_ctor(0, 2, 27);
lean_ctor_set(x_40, 0, x_11);
lean_ctor_set(x_40, 1, x_12);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_13);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 1, x_14);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 2, x_15);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 3, x_16);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 4, x_17);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 5, x_18);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 6, x_19);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 7, x_20);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 8, x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 9, x_22);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 10, x_23);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 11, x_24);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 12, x_25);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 13, x_26);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 14, x_27);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 15, x_28);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 16, x_29);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 17, x_30);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 18, x_31);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 19, x_32);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 20, x_33);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 21, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 22, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 23, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 24, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 25, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 26, x_38);
x_41 = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__1;
x_42 = l_Lean_Meta_Simp_mkContext___redArg(x_40, x_41, x_5, x_1, x_2);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_4);
if (x_43 == 0)
{
return x_4;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_4, 0);
lean_inc(x_44);
lean_dec(x_4);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(x_1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_64; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1);
x_64 = l_Lean_Meta_isRflTheorem(x_1, x_8, x_9);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_Meta_Context_config(x_6);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; uint64_t x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_68 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_69 = lean_ctor_get(x_6, 1);
x_70 = lean_ctor_get(x_6, 2);
x_71 = lean_ctor_get(x_6, 3);
x_72 = lean_ctor_get(x_6, 4);
x_73 = lean_ctor_get(x_6, 5);
x_74 = lean_ctor_get(x_6, 6);
x_75 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_76 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_77 = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0;
x_78 = lean_box(0);
lean_inc(x_1);
x_79 = l_Lean_mkConst(x_1, x_78);
x_80 = lean_unsigned_to_nat(1000u);
x_81 = 1;
x_82 = 0;
x_83 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*1 + 1, x_82);
x_84 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_77);
lean_ctor_set(x_84, 2, x_79);
lean_ctor_set(x_84, 3, x_80);
lean_ctor_set(x_84, 4, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*5, x_81);
lean_ctor_set_uint8(x_84, sizeof(void*)*5 + 1, x_82);
x_85 = lean_unbox(x_65);
lean_dec(x_65);
lean_ctor_set_uint8(x_84, sizeof(void*)*5 + 2, x_85);
x_86 = 2;
lean_ctor_set_uint8(x_66, 9, x_86);
x_87 = l_Lean_Meta_Context_configKey(x_6);
x_88 = 2;
x_89 = lean_uint64_shift_right(x_87, x_88);
x_90 = lean_uint64_shift_left(x_89, x_88);
x_91 = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1;
x_92 = lean_uint64_lor(x_90, x_91);
x_93 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_93, 0, x_66);
lean_ctor_set_uint64(x_93, sizeof(void*)*1, x_92);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc_ref(x_71);
lean_inc_ref(x_70);
lean_inc(x_69);
x_94 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_69);
lean_ctor_set(x_94, 2, x_70);
lean_ctor_set(x_94, 3, x_71);
lean_ctor_set(x_94, 4, x_72);
lean_ctor_set(x_94, 5, x_73);
lean_ctor_set(x_94, 6, x_74);
lean_ctor_set_uint8(x_94, sizeof(void*)*7, x_68);
lean_ctor_set_uint8(x_94, sizeof(void*)*7 + 1, x_75);
lean_ctor_set_uint8(x_94, sizeof(void*)*7 + 2, x_76);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_95 = l_Lean_Meta_Simp_tryTheorem_x3f(x_2, x_84, x_3, x_4, x_5, x_94, x_7, x_8, x_9);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_11 = x_96;
x_12 = lean_box(0);
goto block_63;
}
else
{
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
lean_dec_ref(x_95);
x_11 = x_97;
x_12 = lean_box(0);
goto block_63;
}
else
{
uint8_t x_98; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_98 = !lean_is_exclusive(x_95);
if (x_98 == 0)
{
return x_95;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_95, 0);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
}
else
{
uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_137; lean_object* x_138; uint64_t x_139; uint64_t x_140; uint64_t x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_101 = lean_ctor_get_uint8(x_66, 0);
x_102 = lean_ctor_get_uint8(x_66, 1);
x_103 = lean_ctor_get_uint8(x_66, 2);
x_104 = lean_ctor_get_uint8(x_66, 3);
x_105 = lean_ctor_get_uint8(x_66, 4);
x_106 = lean_ctor_get_uint8(x_66, 5);
x_107 = lean_ctor_get_uint8(x_66, 6);
x_108 = lean_ctor_get_uint8(x_66, 7);
x_109 = lean_ctor_get_uint8(x_66, 8);
x_110 = lean_ctor_get_uint8(x_66, 10);
x_111 = lean_ctor_get_uint8(x_66, 11);
x_112 = lean_ctor_get_uint8(x_66, 12);
x_113 = lean_ctor_get_uint8(x_66, 13);
x_114 = lean_ctor_get_uint8(x_66, 14);
x_115 = lean_ctor_get_uint8(x_66, 15);
x_116 = lean_ctor_get_uint8(x_66, 16);
x_117 = lean_ctor_get_uint8(x_66, 17);
x_118 = lean_ctor_get_uint8(x_66, 18);
lean_dec(x_66);
x_119 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_120 = lean_ctor_get(x_6, 1);
x_121 = lean_ctor_get(x_6, 2);
x_122 = lean_ctor_get(x_6, 3);
x_123 = lean_ctor_get(x_6, 4);
x_124 = lean_ctor_get(x_6, 5);
x_125 = lean_ctor_get(x_6, 6);
x_126 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_127 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_128 = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0;
x_129 = lean_box(0);
lean_inc(x_1);
x_130 = l_Lean_mkConst(x_1, x_129);
x_131 = lean_unsigned_to_nat(1000u);
x_132 = 1;
x_133 = 0;
x_134 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_134, 0, x_1);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_132);
lean_ctor_set_uint8(x_134, sizeof(void*)*1 + 1, x_133);
x_135 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_135, 0, x_128);
lean_ctor_set(x_135, 1, x_128);
lean_ctor_set(x_135, 2, x_130);
lean_ctor_set(x_135, 3, x_131);
lean_ctor_set(x_135, 4, x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*5, x_132);
lean_ctor_set_uint8(x_135, sizeof(void*)*5 + 1, x_133);
x_136 = lean_unbox(x_65);
lean_dec(x_65);
lean_ctor_set_uint8(x_135, sizeof(void*)*5 + 2, x_136);
x_137 = 2;
x_138 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_138, 0, x_101);
lean_ctor_set_uint8(x_138, 1, x_102);
lean_ctor_set_uint8(x_138, 2, x_103);
lean_ctor_set_uint8(x_138, 3, x_104);
lean_ctor_set_uint8(x_138, 4, x_105);
lean_ctor_set_uint8(x_138, 5, x_106);
lean_ctor_set_uint8(x_138, 6, x_107);
lean_ctor_set_uint8(x_138, 7, x_108);
lean_ctor_set_uint8(x_138, 8, x_109);
lean_ctor_set_uint8(x_138, 9, x_137);
lean_ctor_set_uint8(x_138, 10, x_110);
lean_ctor_set_uint8(x_138, 11, x_111);
lean_ctor_set_uint8(x_138, 12, x_112);
lean_ctor_set_uint8(x_138, 13, x_113);
lean_ctor_set_uint8(x_138, 14, x_114);
lean_ctor_set_uint8(x_138, 15, x_115);
lean_ctor_set_uint8(x_138, 16, x_116);
lean_ctor_set_uint8(x_138, 17, x_117);
lean_ctor_set_uint8(x_138, 18, x_118);
x_139 = l_Lean_Meta_Context_configKey(x_6);
x_140 = 2;
x_141 = lean_uint64_shift_right(x_139, x_140);
x_142 = lean_uint64_shift_left(x_141, x_140);
x_143 = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1;
x_144 = lean_uint64_lor(x_142, x_143);
x_145 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_145, 0, x_138);
lean_ctor_set_uint64(x_145, sizeof(void*)*1, x_144);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc_ref(x_122);
lean_inc_ref(x_121);
lean_inc(x_120);
x_146 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_120);
lean_ctor_set(x_146, 2, x_121);
lean_ctor_set(x_146, 3, x_122);
lean_ctor_set(x_146, 4, x_123);
lean_ctor_set(x_146, 5, x_124);
lean_ctor_set(x_146, 6, x_125);
lean_ctor_set_uint8(x_146, sizeof(void*)*7, x_119);
lean_ctor_set_uint8(x_146, sizeof(void*)*7 + 1, x_126);
lean_ctor_set_uint8(x_146, sizeof(void*)*7 + 2, x_127);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_147 = l_Lean_Meta_Simp_tryTheorem_x3f(x_2, x_135, x_3, x_4, x_5, x_146, x_7, x_8, x_9);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
x_11 = x_148;
x_12 = lean_box(0);
goto block_63;
}
else
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec_ref(x_147);
x_11 = x_149;
x_12 = lean_box(0);
goto block_63;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_151 = x_147;
} else {
 lean_dec_ref(x_147);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_150);
return x_152;
}
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_64);
if (x_153 == 0)
{
return x_64;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_64, 0);
lean_inc(x_154);
lean_dec(x_64);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
block_63:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_16, 0);
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
lean_inc_ref(x_17);
x_20 = l_Lean_Meta_reduceMatcher_x3f(x_17, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_inc(x_18);
lean_free_object(x_11);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_16, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_16, 0, x_27);
lean_ctor_set(x_22, 0, x_16);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
lean_ctor_set(x_16, 0, x_28);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
x_30 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_30);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_31 = x_22;
} else {
 lean_dec_ref(x_22);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_19);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 1, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_20, 0, x_33);
return x_20;
}
}
else
{
lean_dec(x_22);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_20, 0);
lean_inc(x_34);
lean_dec(x_20);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_18);
lean_free_object(x_11);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_35 = x_16;
} else {
 lean_dec_ref(x_16);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 2, 1);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_18);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_19);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_34);
lean_ctor_set_tag(x_11, 0);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_11);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_free_object(x_11);
lean_dec(x_16);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_20, 0);
lean_inc(x_43);
lean_dec(x_20);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_11, 0);
lean_inc(x_45);
lean_dec(x_11);
x_46 = lean_ctor_get(x_45, 0);
x_47 = lean_ctor_get(x_45, 1);
x_48 = lean_ctor_get_uint8(x_45, sizeof(void*)*2);
lean_inc_ref(x_46);
x_49 = l_Lean_Meta_reduceMatcher_x3f(x_46, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_52 = x_45;
} else {
 lean_dec_ref(x_45);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 1);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_47);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_48);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_51)) {
 x_57 = lean_alloc_ctor(0, 1, 0);
} else {
 x_57 = x_51;
}
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_50);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_45);
if (lean_is_scalar(x_51)) {
 x_59 = lean_alloc_ctor(0, 1, 0);
} else {
 x_59 = x_51;
}
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_45);
x_60 = lean_ctor_get(x_49, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_61 = x_49;
} else {
 lean_dec_ref(x_49);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_box(0);
x_11 = 1;
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_unfold___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_unfold___lam__1___closed__0;
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_unfold___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_unfold___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_unfold___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_unfold___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_unfold___closed__3;
x_4 = l_Lean_Meta_unfold___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_unfold___closed__5;
x_2 = l_Lean_Meta_unfold___closed__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_unfold___closed__6;
x_2 = l_Lean_Meta_unfold___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_9 = l_Lean_Meta_getUnfoldEqnFor_x3f(x_2, x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(x_3, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_unfold___lam__0___boxed), 9, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_unfold___lam__1___boxed), 9, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_unfold___lam__2___boxed), 9, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_unfold___lam__3___boxed), 9, 0);
x_18 = l_Lean_Meta_unfold___closed__7;
x_19 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed), 10, 1);
lean_closure_set(x_19, 0, x_11);
x_20 = 1;
x_21 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_20);
x_22 = l_Lean_Meta_Simp_main(x_1, x_13, x_18, x_21, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec_ref(x_3);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_unfold___lam__4___boxed), 2, 1);
lean_closure_set(x_35, 0, x_2);
x_36 = l_Lean_Meta_deltaExpand(x_1, x_35, x_5, x_6);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_box(0);
x_40 = 1;
x_41 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_40);
lean_ctor_set(x_36, 0, x_41);
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_box(0);
x_44 = 1;
x_45 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_36, 0);
lean_inc(x_48);
lean_dec(x_36);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_50 = !lean_is_exclusive(x_9);
if (x_50 == 0)
{
return x_9;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_9, 0);
lean_inc(x_51);
lean_dec(x_9);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_unfold___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_unfold___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_unfold___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_unfold___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_unfold___lam__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_unfold(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_unfoldTarget___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic `unfold` failed to unfold `", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_unfoldTarget___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_unfoldTarget___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` in", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_unfoldTarget___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(x_9, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_11);
x_12 = l_Lean_Meta_unfold(x_11, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_expr_eqv(x_14, x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = l_Lean_Meta_applySimpResultToTarget(x_1, x_11, x_13, x_3, x_4, x_5, x_6);
lean_dec(x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_1);
x_17 = l_Lean_Meta_unfoldTarget___lam__0___closed__1;
x_18 = 0;
x_19 = l_Lean_MessageData_ofConstName(x_2, x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_unfoldTarget___lam__0___closed__3;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_indentExpr(x_11);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(x_24, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
return x_8;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
lean_dec(x_8);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldTarget___lam__0___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_unfoldTarget___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_unfoldTarget(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, lean_box(0));
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Unfold", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.unfoldLocalDecl", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2;
x_2 = lean_unsigned_to_nat(94u);
x_3 = lean_unsigned_to_nat(45u);
x_4 = l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1;
x_5 = l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_4);
lean_inc(x_1);
x_9 = l_Lean_FVarId_getType___redArg(x_1, x_4, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_10);
x_11 = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(x_10, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_2);
x_13 = l_Lean_Meta_unfold(x_12, x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_expr_eqv(x_15, x_10);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_17 = l_Lean_Meta_applySimpResultToLocalDecl(x_3, x_1, x_14, x_16, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_17);
lean_dec(x_19);
x_22 = l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3;
x_23 = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(x_22, x_4, x_5, x_6, x_7);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
x_28 = l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3;
x_29 = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(x_28, x_4, x_5, x_6, x_7);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_17, 0);
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
x_33 = l_Lean_Meta_unfoldTarget___lam__0___closed__1;
x_34 = 0;
x_35 = l_Lean_MessageData_ofConstName(x_2, x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_unfoldTarget___lam__0___closed__3;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_indentExpr(x_10);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(x_40, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_13, 0);
lean_inc(x_46);
lean_dec(x_13);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_9);
if (x_48 == 0)
{
return x_9;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_9, 0);
lean_inc(x_49);
lean_dec(x_9);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_unfoldLocalDecl___lam__0___boxed), 8, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_1);
x_10 = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3___redArg(x_1, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_unfoldLocalDecl___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_unfoldLocalDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_zetaDeltaTarget___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(x_9, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_Meta_zetaDeltaTarget___lam__0___closed__0;
lean_inc(x_2);
x_13 = lean_array_push(x_12, x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_11);
x_14 = l_Lean_Meta_zetaDeltaFVars(x_11, x_13, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_expr_eqv(x_15, x_11);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_2);
x_17 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_15, x_3, x_4, x_5, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_1);
x_18 = l_Lean_Meta_unfoldTarget___lam__0___closed__1;
x_19 = l_Lean_Expr_fvar___override(x_2);
x_20 = l_Lean_MessageData_ofExpr(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_unfoldTarget___lam__0___closed__3;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_indentExpr(x_11);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(x_25, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_34);
lean_dec(x_8);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaTarget___lam__0___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_zetaDeltaTarget___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_zetaDeltaTarget(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_4);
lean_inc(x_1);
x_9 = l_Lean_FVarId_getType___redArg(x_1, x_4, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_10);
x_11 = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(x_10, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Meta_zetaDeltaTarget___lam__0___closed__0;
x_14 = lean_array_push(x_13, x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_15 = l_Lean_Meta_zetaDeltaFVars(x_12, x_14, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_expr_eqv(x_16, x_10);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_10);
x_18 = l_Lean_MVarId_replaceLocalDeclDefEq(x_3, x_1, x_16, x_4, x_5, x_6, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_3);
x_19 = l_Lean_Meta_unfoldTarget___lam__0___closed__1;
x_20 = l_Lean_Expr_fvar___override(x_1);
x_21 = l_Lean_MessageData_ofExpr(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_unfoldTarget___lam__0___closed__3;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_indentExpr(x_10);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(x_26, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_9);
if (x_34 == 0)
{
return x_9;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_9, 0);
lean_inc(x_35);
lean_dec(x_9);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed), 8, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_1);
x_10 = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__3___redArg(x_1, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_zetaDeltaLocalDecl___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_zetaDeltaLocalDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0 = _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0);
l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__1 = _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__1);
l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0 = _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0);
l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1 = _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1();
l_Lean_Meta_unfold___lam__1___closed__0 = _init_l_Lean_Meta_unfold___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_unfold___lam__1___closed__0);
l_Lean_Meta_unfold___closed__0 = _init_l_Lean_Meta_unfold___closed__0();
lean_mark_persistent(l_Lean_Meta_unfold___closed__0);
l_Lean_Meta_unfold___closed__1 = _init_l_Lean_Meta_unfold___closed__1();
lean_mark_persistent(l_Lean_Meta_unfold___closed__1);
l_Lean_Meta_unfold___closed__2 = _init_l_Lean_Meta_unfold___closed__2();
lean_mark_persistent(l_Lean_Meta_unfold___closed__2);
l_Lean_Meta_unfold___closed__3 = _init_l_Lean_Meta_unfold___closed__3();
lean_mark_persistent(l_Lean_Meta_unfold___closed__3);
l_Lean_Meta_unfold___closed__4 = _init_l_Lean_Meta_unfold___closed__4();
lean_mark_persistent(l_Lean_Meta_unfold___closed__4);
l_Lean_Meta_unfold___closed__5 = _init_l_Lean_Meta_unfold___closed__5();
lean_mark_persistent(l_Lean_Meta_unfold___closed__5);
l_Lean_Meta_unfold___closed__6 = _init_l_Lean_Meta_unfold___closed__6();
lean_mark_persistent(l_Lean_Meta_unfold___closed__6);
l_Lean_Meta_unfold___closed__7 = _init_l_Lean_Meta_unfold___closed__7();
lean_mark_persistent(l_Lean_Meta_unfold___closed__7);
l_Lean_Meta_unfoldTarget___lam__0___closed__0 = _init_l_Lean_Meta_unfoldTarget___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_unfoldTarget___lam__0___closed__0);
l_Lean_Meta_unfoldTarget___lam__0___closed__1 = _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_unfoldTarget___lam__0___closed__1);
l_Lean_Meta_unfoldTarget___lam__0___closed__2 = _init_l_Lean_Meta_unfoldTarget___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_unfoldTarget___lam__0___closed__2);
l_Lean_Meta_unfoldTarget___lam__0___closed__3 = _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_unfoldTarget___lam__0___closed__3);
l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0 = _init_l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0);
l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0 = _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0);
l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1 = _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1);
l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2 = _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2);
l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3 = _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3);
l_Lean_Meta_zetaDeltaTarget___lam__0___closed__0 = _init_l_Lean_Meta_zetaDeltaTarget___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_zetaDeltaTarget___lam__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
