// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Congr
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InferType import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Simp.CongrInfo
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
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go_spec__0___closed__0;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrThm___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__3;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6;
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___closed__1;
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4;
lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrThm___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1;
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_congrArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_congrArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__0;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getCongrInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_3);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*6);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = x_3;
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_16; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
lean_inc(x_3);
lean_inc_ref(x_2);
x_17 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
x_9 = x_3;
x_10 = lean_box(0);
goto block_13;
}
else
{
uint8_t x_18; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_app___override(x_1, x_2);
x_12 = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(x_11, x_9);
lean_dec(x_9);
return x_12;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrArg", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_10 = l_Lean_Meta_Sym_inferType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_11);
x_12 = l_Lean_Meta_Sym_getLevel(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_14 = l_Lean_Meta_Sym_inferType(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_15);
x_16 = l_Lean_Meta_Sym_getLevel(x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_mkConst(x_3, x_21);
x_23 = l_Lean_mkAppB(x_22, x_11, x_15);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_mkConst(x_3, x_27);
x_29 = l_Lean_mkAppB(x_28, x_11, x_15);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_14;
}
}
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrFun'", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec_ref(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_15);
lean_inc_ref(x_2);
x_17 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr_spec__0(x_2, x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2;
lean_inc_ref(x_3);
x_20 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_19, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_mkApp4(x_22, x_3, x_15, x_2, x_16);
x_24 = 0;
lean_ctor_set(x_5, 1, x_23);
lean_ctor_set(x_5, 0, x_18);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_24);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Lean_mkApp4(x_25, x_3, x_15, x_2, x_16);
x_27 = 0;
lean_ctor_set(x_5, 1, x_26);
lean_ctor_set(x_5, 0, x_18);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_27);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_5);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_18);
lean_free_object(x_5);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_free_object(x_5);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_35);
lean_inc_ref(x_2);
x_37 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr_spec__0(x_2, x_35, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2;
lean_inc_ref(x_3);
x_40 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_39, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = l_Lean_mkApp4(x_41, x_3, x_35, x_2, x_36);
x_44 = 0;
x_45 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_44);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_38);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_48 = x_40;
} else {
 lean_dec_ref(x_40);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_51 = x_37;
} else {
 lean_dec_ref(x_37);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_53; 
lean_dec_ref(x_5);
x_53 = !lean_is_exclusive(x_4);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_4, 0);
x_55 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_3);
lean_inc_ref(x_54);
x_56 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr_spec__0(x_54, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4;
lean_inc_ref(x_3);
x_59 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_58, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = l_Lean_mkApp4(x_61, x_2, x_54, x_55, x_3);
x_63 = 0;
lean_ctor_set(x_4, 1, x_62);
lean_ctor_set(x_4, 0, x_57);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_63);
lean_ctor_set(x_59, 0, x_4);
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
lean_dec(x_59);
x_65 = l_Lean_mkApp4(x_64, x_2, x_54, x_55, x_3);
x_66 = 0;
lean_ctor_set(x_4, 1, x_65);
lean_ctor_set(x_4, 0, x_57);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_66);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_4);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_57);
lean_free_object(x_4);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_68 = !lean_is_exclusive(x_59);
if (x_68 == 0)
{
return x_59;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
lean_dec(x_59);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_free_object(x_4);
lean_dec_ref(x_55);
lean_dec_ref(x_54);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_56);
if (x_71 == 0)
{
return x_56;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_56, 0);
lean_inc(x_72);
lean_dec(x_56);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_4, 0);
x_75 = lean_ctor_get(x_4, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_4);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_3);
lean_inc_ref(x_74);
x_76 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr_spec__0(x_74, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4;
lean_inc_ref(x_3);
x_79 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_78, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = l_Lean_mkApp4(x_80, x_2, x_74, x_75, x_3);
x_83 = 0;
x_84 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_83);
if (lean_is_scalar(x_81)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_81;
}
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_77);
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_86 = lean_ctor_get(x_79, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_87 = x_79;
} else {
 lean_dec_ref(x_79);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_76, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_90 = x_76;
} else {
 lean_dec_ref(x_76);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_93);
lean_dec_ref(x_4);
x_94 = !lean_is_exclusive(x_5);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_5, 0);
x_96 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_95);
lean_inc_ref(x_92);
x_97 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr_spec__0(x_92, x_95, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6;
lean_inc_ref(x_3);
x_100 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_99, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = l_Lean_mkApp6(x_102, x_2, x_92, x_3, x_95, x_93, x_96);
x_104 = 0;
lean_ctor_set(x_5, 1, x_103);
lean_ctor_set(x_5, 0, x_98);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_104);
lean_ctor_set(x_100, 0, x_5);
return x_100;
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
lean_dec(x_100);
x_106 = l_Lean_mkApp6(x_105, x_2, x_92, x_3, x_95, x_93, x_96);
x_107 = 0;
lean_ctor_set(x_5, 1, x_106);
lean_ctor_set(x_5, 0, x_98);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_107);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_5);
return x_108;
}
}
else
{
uint8_t x_109; 
lean_dec(x_98);
lean_free_object(x_5);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_109 = !lean_is_exclusive(x_100);
if (x_109 == 0)
{
return x_100;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_100, 0);
lean_inc(x_110);
lean_dec(x_100);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_free_object(x_5);
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_112 = !lean_is_exclusive(x_97);
if (x_112 == 0)
{
return x_97;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_97, 0);
lean_inc(x_113);
lean_dec(x_97);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_5, 0);
x_116 = lean_ctor_get(x_5, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_115);
lean_inc_ref(x_92);
x_117 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr_spec__0(x_92, x_115, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6;
lean_inc_ref(x_3);
x_120 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_3, x_1, x_119, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = l_Lean_mkApp6(x_121, x_2, x_92, x_3, x_115, x_93, x_116);
x_124 = 0;
x_125 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_125, 0, x_118);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*2, x_124);
if (lean_is_scalar(x_122)) {
 x_126 = lean_alloc_ctor(0, 1, 0);
} else {
 x_126 = x_122;
}
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_118);
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_127 = lean_ctor_get(x_120, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_128 = x_120;
} else {
 lean_dec_ref(x_120);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec_ref(x_116);
lean_dec_ref(x_115);
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_130 = lean_ctor_get(x_117, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_131 = x_117;
} else {
 lean_dec_ref(x_117);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_130);
return x_132;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(x_2, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrFun", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to build congruence proof, function expected", 51, 51);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_2);
x_12 = l_Lean_Meta_Sym_inferType(x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_14 = l_Lean_Meta_whnfD(x_13, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 7)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_15);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_3);
x_18 = l_Lean_Meta_Sym_inferType(x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_19);
x_20 = l_Lean_Meta_Sym_getLevel(x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_22 = l_Lean_Meta_Sym_inferType(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_24 = l_Lean_Meta_Sym_getLevel(x_23, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc_ref(x_3);
lean_inc_ref(x_4);
x_26 = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr_spec__0(x_4, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = 0;
lean_inc(x_19);
x_30 = l_Lean_mkLambda(x_16, x_29, x_19, x_17);
x_31 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1;
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_mkConst(x_31, x_34);
x_36 = l_Lean_mkApp6(x_35, x_19, x_30, x_2, x_4, x_5, x_3);
x_37 = 0;
x_38 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_37);
lean_ctor_set(x_26, 0, x_38);
return x_26;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_39 = lean_ctor_get(x_26, 0);
lean_inc(x_39);
lean_dec(x_26);
x_40 = 0;
lean_inc(x_19);
x_41 = l_Lean_mkLambda(x_16, x_40, x_19, x_17);
x_42 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1;
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_25);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_21);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_mkConst(x_42, x_45);
x_47 = l_Lean_mkApp6(x_46, x_19, x_41, x_2, x_4, x_5, x_3);
x_48 = 0;
x_49 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_51 = !lean_is_exclusive(x_26);
if (x_51 == 0)
{
return x_26;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_26, 0);
lean_inc(x_52);
lean_dec(x_26);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_54 = !lean_is_exclusive(x_24);
if (x_54 == 0)
{
return x_24;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_24, 0);
lean_inc(x_55);
lean_dec(x_24);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_57 = !lean_is_exclusive(x_22);
if (x_57 == 0)
{
return x_22;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_22, 0);
lean_inc(x_58);
lean_dec(x_22);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_20);
if (x_60 == 0)
{
return x_20;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_20, 0);
lean_inc(x_61);
lean_dec(x_20);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_63 = !lean_is_exclusive(x_18);
if (x_63 == 0)
{
return x_18;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_18, 0);
lean_inc(x_64);
lean_dec(x_18);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_66 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3;
x_67 = l_Lean_indentExpr(x_2);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(x_68, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_70 = !lean_is_exclusive(x_14);
if (x_70 == 0)
{
return x_14;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_14, 0);
lean_inc(x_71);
lean_dec(x_14);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_12);
if (x_73 == 0)
{
return x_12;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_12, 0);
lean_inc(x_74);
lean_dec(x_12);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go_spec__0___closed__0;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Sym.Simp.Congr", 24, 24);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Sym.Simp.Congr.0.Lean.Meta.Sym.Simp.congrFixedPrefix.go", 74, 74);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__2;
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(104u);
x_4 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__1;
x_5 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_eq(x_2, x_1);
if (x_13 == 0)
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_15);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_2, x_16);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_14);
x_18 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go(x_1, x_17, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_15);
x_20 = lean_sym_simp(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg(x_3, x_14, x_15, x_19, x_21, x_7, x_8, x_9, x_10, x_11);
return x_22;
}
else
{
lean_dec(x_19);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
return x_20;
}
}
else
{
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_18;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_3);
x_23 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__3;
x_24 = l_panic___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go_spec__0(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_25 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_panic___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Expr_getAppNumArgs(x_1);
x_14 = lean_nat_dec_le(x_13, x_2);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_nat_add(x_2, x_3);
x_16 = lean_nat_dec_lt(x_15, x_13);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go(x_2, x_13, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_18, 0, x_14);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_20 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Sym.Simp.Congr.0.Lean.Meta.Sym.Simp.congrInterlaced.go", 73, 73);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__2;
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(135u);
x_4 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___closed__0;
x_5 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_2, x_17);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_15);
x_19 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg(x_1, x_18, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_array_fget_borrowed(x_1, x_18);
lean_dec(x_18);
x_23 = lean_unbox(x_22);
if (x_23 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_24; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_21, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 0, 1);
x_27 = lean_unbox(x_22);
lean_ctor_set_uint8(x_26, 0, x_27);
lean_ctor_set(x_19, 0, x_26);
return x_19;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_19);
x_28 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_29);
lean_dec_ref(x_21);
x_30 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_3, x_15, x_16, x_28, x_29, x_7, x_8, x_9, x_10, x_11);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_free_object(x_19);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_16);
x_31 = lean_sym_simp(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg(x_3, x_15, x_16, x_21, x_32, x_7, x_8, x_9, x_10, x_11);
return x_33;
}
else
{
lean_dec(x_21);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
return x_31;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_array_fget_borrowed(x_1, x_18);
lean_dec(x_18);
x_36 = lean_unbox(x_35);
if (x_36 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
if (lean_is_exclusive(x_34)) {
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 0, 1);
} else {
 x_38 = x_37;
}
x_39 = lean_unbox(x_35);
lean_ctor_set_uint8(x_38, 0, x_39);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_42);
lean_dec_ref(x_34);
x_43 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg(x_3, x_15, x_16, x_41, x_42, x_7, x_8, x_9, x_10, x_11);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_16);
x_44 = lean_sym_simp(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg(x_3, x_15, x_16, x_34, x_45, x_7, x_8, x_9, x_10, x_11);
return x_46;
}
else
{
lean_dec(x_34);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
return x_44;
}
}
}
}
else
{
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_19;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_3);
x_47 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___closed__1;
x_48 = l_panic___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go_spec__0(x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_49 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Expr_getAppNumArgs(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_lt(x_15, x_12);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg(x_2, x_12, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_18, 0, x_14);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_20 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrThm___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrThm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrThm___redArg();
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrThm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrThm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrThm___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrThm___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_congrArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_getAppFn(x_1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_12 = l_Lean_Meta_Sym_getCongrInfo(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_15 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_12);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix(x_1, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_17);
lean_dec(x_16);
return x_18;
}
case 2:
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_12);
x_19 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_14);
x_20 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_19);
return x_20;
}
default: 
{
lean_object* x_21; 
lean_free_object(x_12);
lean_dec_ref(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrThm___redArg();
return x_21;
}
}
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
switch (lean_obj_tag(x_22)) {
case 0:
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_23 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0;
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
case 1:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec_ref(x_22);
x_27 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix(x_1, x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_26);
lean_dec(x_25);
return x_27;
}
case 2:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_28);
lean_dec_ref(x_22);
x_29 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced(x_1, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_28);
return x_29;
}
default: 
{
lean_object* x_30; 
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_30 = l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrThm___redArg();
return x_30;
}
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_congrArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Sym_Simp_congrArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_CongrInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Congr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__0);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__1);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__2);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__3);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__4);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__5);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongr___redArg___closed__6);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__0);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__1);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__2);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_mkCongrFun___redArg___closed__3);
l_panic___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go_spec__0___closed__0 = _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go_spec__0___closed__0);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__0);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__1);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__2);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__3 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrFixedPrefix_go___closed__3);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___closed__0);
l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_Congr_0__Lean_Meta_Sym_Simp_congrInterlaced_go___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
