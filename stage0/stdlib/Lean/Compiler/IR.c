// Lean compiler output
// Module: Lean.Compiler.IR
// Imports: public import Lean.Compiler.IR.AddExtern public import Lean.Compiler.IR.Basic public import Lean.Compiler.IR.Format public import Lean.Compiler.IR.CompilerM public import Lean.Compiler.IR.PushProj public import Lean.Compiler.IR.ElimDeadVars public import Lean.Compiler.IR.SimpCase public import Lean.Compiler.IR.ResetReuse public import Lean.Compiler.IR.NormIds public import Lean.Compiler.IR.Checker public import Lean.Compiler.IR.Borrow public import Lean.Compiler.IR.Boxing public import Lean.Compiler.IR.RC public import Lean.Compiler.IR.ExpandResetReuse public import Lean.Compiler.IR.UnboxResult public import Lean.Compiler.IR.EmitC public import Lean.Compiler.IR.Sorry public import Lean.Compiler.IR.ToIR public import Lean.Compiler.IR.ToIRType public import Lean.Compiler.IR.Meta public import Lean.Compiler.IR.Toposort public import Lean.Compiler.IR.SimpleGroundExpr public import Lean.Compiler.IR.LLVMBindings public import Lean.Compiler.IR.EmitLLVM
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
static lean_object* l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
lean_object* l_Lean_IR_Decl_simpCase(lean_object*);
static lean_object* l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
lean_object* l_Lean_IR_inferBorrow___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__22;
static lean_object* l_Lean_IR_compile___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* l_Lean_IR_compile___closed__28;
static lean_object* l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
static lean_object* l_Lean_IR_compile___closed__24;
static lean_object* l_Lean_IR_compile___closed__17;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__2;
static lean_object* l_Lean_IR_compile___closed__21;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_compiler_reuse;
static lean_object* l_Lean_IR_compile___closed__27;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l_Lean_IR_compile___closed__3;
lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__11;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l_Lean_IR_compile___closed__26;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_IR_compile___closed__10;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l_Lean_IR_compile___closed__14;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_pushProj(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_IR_explicitBoxing___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__6(size_t, size_t, lean_object*);
static lean_object* l_Lean_IR_compile___closed__0;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l_Lean_IR_compile___closed__18;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__20;
static lean_object* l_Lean_IR_compile___closed__5;
static lean_object* l_Lean_IR_compile___closed__19;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__7(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_IR_compile___closed__16;
static lean_object* l_Lean_IR_compile___closed__23;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
lean_object* l_Lean_IR_toposortDecls(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__25;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_IR_compile_spec__5(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l_Lean_IR_explicitRC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_IR_compile_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_compile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__7;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_IR_compile___closed__8;
LEAN_EXPORT lean_object* l_Lean_IR_compile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_object* l_Lean_IR_inferMeta(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_IR_compile___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__0(size_t, size_t, lean_object*);
static lean_object* l_Lean_IR_compile___closed__15;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
lean_object* l_Lean_IR_updateSorryDep(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_IR_compile___closed__4;
lean_object* l_Lean_IR_Decl_detectSimpleGround(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__4(size_t, size_t, lean_object*);
static lean_object* l_Lean_IR_compile___closed__1;
static lean_object* l_Lean_IR_compile___closed__6;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_IR_compile___closed__12;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
static lean_object* l_Lean_IR_compile___closed__29;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_alloc_ctor(1, 0, 1);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, 0, x_9);
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_7);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 0, 1);
x_21 = lean_unbox(x_18);
lean_ctor_set_uint8(x_20, 0, x_21);
lean_inc(x_1);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_19);
lean_inc(x_1);
x_23 = lean_register_option(x_1, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_24 = x_23;
} else {
 lean_dec_ref(x_23);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_18);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_1);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_28 = x_23;
} else {
 lean_dec_ref(x_23);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reuse", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_2 = l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("heuristically insert reset/reuse instruction pairs", 50, 50);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IR", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_2 = l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_3 = l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_4 = l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_3 = l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_4 = l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_5 = l_Lean_Option_register___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_IR_compile_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_IR_compile_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_IR_compile_spec__5(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_IR_Decl_elimDead(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__6(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_IR_Decl_expandResetReuse(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__6(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_1, x_2);
x_10 = l_Lean_IR_Decl_detectSimpleGround(x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
else
{
return x_10;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc_ref(x_1);
x_9 = l_Lean_IR_Decl_insertResetReuse(x_1, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__7(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_IR_Decl_simpCase(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_IR_Decl_pushProj(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_IR_Decl_normalizeIds(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__4(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__1;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("push_proj", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__4;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__7;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elim_dead", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__10;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp_case", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__12;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__13;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("borrow", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__15;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__16;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("boxing", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__18;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__19;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rc", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__21;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__22;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expand_reset_reuse", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__24;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__25;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reset_reuse", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__27;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__28;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_IR_compile___closed__1;
x_30 = l_Lean_IR_compile___closed__2;
lean_inc_ref(x_1);
x_31 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_30, x_29, x_1, x_2, x_3);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec_ref(x_31);
lean_inc_ref(x_1);
x_32 = l_Lean_IR_checkDecls(x_1, x_2, x_3);
if (lean_obj_tag(x_32) == 0)
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_130; lean_object* x_131; 
lean_dec_ref(x_32);
x_33 = lean_array_size(x_1);
x_34 = 0;
x_35 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__0(x_33, x_34, x_1);
x_36 = l_Lean_IR_compile___closed__4;
x_130 = l_Lean_IR_compile___closed__5;
lean_inc_ref(x_35);
x_131 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_130, x_36, x_35, x_2, x_3);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_dec_ref(x_131);
x_132 = lean_ctor_get(x_2, 2);
x_133 = l_Lean_IR_compiler_reuse;
x_134 = l_Lean_Option_get___at___00Lean_IR_compile_spec__5(x_132, x_133);
if (x_134 == 0)
{
x_72 = x_35;
x_73 = x_2;
x_74 = x_3;
x_75 = lean_box(0);
goto block_129;
}
else
{
lean_object* x_135; lean_object* x_136; size_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_st_ref_get(x_3);
x_136 = lean_ctor_get(x_135, 0);
lean_inc_ref(x_136);
lean_dec(x_135);
x_137 = lean_array_size(x_35);
x_138 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__7(x_136, x_137, x_34, x_35);
x_139 = l_Lean_IR_compile___closed__28;
x_140 = l_Lean_IR_compile___closed__29;
lean_inc_ref(x_138);
x_141 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_140, x_139, x_138, x_2, x_3);
if (lean_obj_tag(x_141) == 0)
{
lean_dec_ref(x_141);
x_72 = x_138;
x_73 = x_2;
x_74 = x_3;
x_75 = lean_box(0);
goto block_129;
}
else
{
uint8_t x_142; 
lean_dec_ref(x_138);
lean_dec(x_3);
lean_dec_ref(x_2);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
return x_141;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
}
}
else
{
uint8_t x_145; 
lean_dec_ref(x_35);
lean_dec(x_3);
lean_dec_ref(x_2);
x_145 = !lean_is_exclusive(x_131);
if (x_145 == 0)
{
return x_131;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_131, 0);
lean_inc(x_146);
lean_dec(x_131);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
}
block_71:
{
size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_array_size(x_37);
x_42 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__0(x_41, x_34, x_37);
x_43 = l_Lean_IR_compile___closed__5;
lean_inc_ref(x_42);
x_44 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_43, x_36, x_42, x_38, x_39);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec_ref(x_44);
x_45 = l_Lean_IR_updateSorryDep(x_42, x_38, x_39);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_Lean_IR_compile___closed__7;
x_48 = l_Lean_IR_compile___closed__8;
lean_inc(x_46);
x_49 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_48, x_47, x_46, x_38, x_39);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
lean_dec_ref(x_49);
lean_inc(x_46);
x_50 = l_Lean_IR_checkDecls(x_46, x_38, x_39);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec_ref(x_50);
lean_inc(x_39);
lean_inc_ref(x_38);
x_51 = l_Lean_IR_toposortDecls(x_46, x_38, x_39);
lean_dec(x_46);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_array_get_size(x_52);
x_55 = lean_nat_dec_lt(x_53, x_54);
if (x_55 == 0)
{
x_5 = x_38;
x_6 = x_52;
x_7 = x_39;
x_8 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_box(0);
x_57 = lean_nat_dec_le(x_54, x_54);
if (x_57 == 0)
{
if (x_55 == 0)
{
x_5 = x_38;
x_6 = x_52;
x_7 = x_39;
x_8 = lean_box(0);
goto block_20;
}
else
{
size_t x_58; lean_object* x_59; 
x_58 = lean_usize_of_nat(x_54);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1(x_52, x_34, x_58, x_56, x_38, x_39);
x_21 = x_38;
x_22 = x_52;
x_23 = x_39;
x_24 = x_59;
goto block_28;
}
}
else
{
size_t x_60; lean_object* x_61; 
x_60 = lean_usize_of_nat(x_54);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_compile_spec__1(x_52, x_34, x_60, x_56, x_38, x_39);
x_21 = x_38;
x_22 = x_52;
x_23 = x_39;
x_24 = x_61;
goto block_28;
}
}
}
else
{
lean_dec(x_39);
lean_dec_ref(x_38);
return x_51;
}
}
else
{
uint8_t x_62; 
lean_dec(x_46);
lean_dec(x_39);
lean_dec_ref(x_38);
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
return x_50;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
lean_dec(x_50);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_46);
lean_dec(x_39);
lean_dec_ref(x_38);
x_65 = !lean_is_exclusive(x_49);
if (x_65 == 0)
{
return x_49;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_49, 0);
lean_inc(x_66);
lean_dec(x_49);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
lean_dec(x_39);
lean_dec_ref(x_38);
return x_45;
}
}
else
{
uint8_t x_68; 
lean_dec_ref(x_42);
lean_dec(x_39);
lean_dec_ref(x_38);
x_68 = !lean_is_exclusive(x_44);
if (x_68 == 0)
{
return x_44;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_44, 0);
lean_inc(x_69);
lean_dec(x_44);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
block_129:
{
size_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_array_size(x_72);
x_77 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__2(x_76, x_34, x_72);
x_78 = l_Lean_IR_compile___closed__10;
x_79 = l_Lean_IR_compile___closed__11;
lean_inc_ref(x_77);
x_80 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_79, x_78, x_77, x_73, x_74);
if (lean_obj_tag(x_80) == 0)
{
size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec_ref(x_80);
x_81 = lean_array_size(x_77);
x_82 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__3(x_81, x_34, x_77);
x_83 = l_Lean_IR_compile___closed__13;
x_84 = l_Lean_IR_compile___closed__14;
lean_inc_ref(x_82);
x_85 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_84, x_83, x_82, x_73, x_74);
if (lean_obj_tag(x_85) == 0)
{
size_t x_86; lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_85);
x_86 = lean_array_size(x_82);
x_87 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__4(x_86, x_34, x_82);
x_88 = l_Lean_IR_inferBorrow___redArg(x_87, x_74);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = l_Lean_IR_compile___closed__16;
x_91 = l_Lean_IR_compile___closed__17;
lean_inc(x_89);
x_92 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_91, x_90, x_89, x_73, x_74);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
lean_dec_ref(x_92);
x_93 = l_Lean_IR_explicitBoxing___redArg(x_89, x_74);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = l_Lean_IR_compile___closed__19;
x_96 = l_Lean_IR_compile___closed__20;
lean_inc(x_94);
x_97 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_96, x_95, x_94, x_73, x_74);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
lean_dec_ref(x_97);
x_98 = l_Lean_IR_explicitRC___redArg(x_94, x_74);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = l_Lean_IR_compile___closed__22;
x_101 = l_Lean_IR_compile___closed__23;
lean_inc(x_99);
x_102 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_101, x_100, x_99, x_73, x_74);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec_ref(x_102);
x_103 = lean_ctor_get(x_73, 2);
x_104 = l_Lean_IR_compiler_reuse;
x_105 = l_Lean_Option_get___at___00Lean_IR_compile_spec__5(x_103, x_104);
if (x_105 == 0)
{
x_37 = x_99;
x_38 = x_73;
x_39 = x_74;
x_40 = lean_box(0);
goto block_71;
}
else
{
size_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_array_size(x_99);
x_107 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_compile_spec__6(x_106, x_34, x_99);
x_108 = l_Lean_IR_compile___closed__25;
x_109 = l_Lean_IR_compile___closed__26;
lean_inc_ref(x_107);
x_110 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_109, x_108, x_107, x_73, x_74);
if (lean_obj_tag(x_110) == 0)
{
lean_dec_ref(x_110);
x_37 = x_107;
x_38 = x_73;
x_39 = x_74;
x_40 = lean_box(0);
goto block_71;
}
else
{
uint8_t x_111; 
lean_dec_ref(x_107);
lean_dec(x_74);
lean_dec_ref(x_73);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
return x_110;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_99);
lean_dec(x_74);
lean_dec_ref(x_73);
x_114 = !lean_is_exclusive(x_102);
if (x_114 == 0)
{
return x_102;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_102, 0);
lean_inc(x_115);
lean_dec(x_102);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
}
else
{
lean_dec(x_74);
lean_dec_ref(x_73);
return x_98;
}
}
else
{
uint8_t x_117; 
lean_dec(x_94);
lean_dec(x_74);
lean_dec_ref(x_73);
x_117 = !lean_is_exclusive(x_97);
if (x_117 == 0)
{
return x_97;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_97, 0);
lean_inc(x_118);
lean_dec(x_97);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
else
{
lean_dec(x_74);
lean_dec_ref(x_73);
return x_93;
}
}
else
{
uint8_t x_120; 
lean_dec(x_89);
lean_dec(x_74);
lean_dec_ref(x_73);
x_120 = !lean_is_exclusive(x_92);
if (x_120 == 0)
{
return x_92;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_92, 0);
lean_inc(x_121);
lean_dec(x_92);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
else
{
lean_dec(x_74);
lean_dec_ref(x_73);
return x_88;
}
}
else
{
uint8_t x_123; 
lean_dec_ref(x_82);
lean_dec(x_74);
lean_dec_ref(x_73);
x_123 = !lean_is_exclusive(x_85);
if (x_123 == 0)
{
return x_85;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_85, 0);
lean_inc(x_124);
lean_dec(x_85);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec_ref(x_77);
lean_dec(x_74);
lean_dec_ref(x_73);
x_126 = !lean_is_exclusive(x_80);
if (x_126 == 0)
{
return x_80;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_80, 0);
lean_inc(x_127);
lean_dec(x_80);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_148 = !lean_is_exclusive(x_32);
if (x_148 == 0)
{
return x_32;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_32, 0);
lean_inc(x_149);
lean_dec(x_32);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_151 = !lean_is_exclusive(x_31);
if (x_151 == 0)
{
return x_31;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_31, 0);
lean_inc(x_152);
lean_dec(x_31);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
block_20:
{
lean_object* x_9; 
x_9 = l_Lean_IR_addDecls(x_6, x_5, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec_ref(x_9);
x_10 = l_Lean_IR_inferMeta(x_6, x_5, x_7);
lean_dec(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec_ref(x_6);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
block_28:
{
if (lean_obj_tag(x_24) == 0)
{
lean_dec_ref(x_24);
x_5 = x_21;
x_6 = x_22;
x_7 = x_23;
x_8 = lean_box(0);
goto block_20;
}
else
{
uint8_t x_25; 
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
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
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_compile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_compile(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ir", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_2 = l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(640659120u);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hygCtx", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_IR_compile___closed__0;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_IR_compile___closed__6;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_3 = 0;
x_4 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
lean_dec_ref(x_5);
x_6 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_7 = 1;
x_8 = l_Lean_registerTraceClass(x_6, x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_8);
x_9 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_;
x_10 = l_Lean_registerTraceClass(x_9, x_7, x_4);
return x_10;
}
else
{
return x_8;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_PushProj(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ElimDeadVars(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_SimpCase(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ResetReuse(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Checker(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Borrow(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Boxing(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_RC(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ExpandResetReuse(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_UnboxResult(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_EmitC(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Sorry(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Meta(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Toposort(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_SimpleGroundExpr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_LLVMBindings(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_EmitLLVM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_AddExtern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_PushProj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ElimDeadVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_SimpCase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Checker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Borrow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Boxing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_RC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ExpandResetReuse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_UnboxResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIRType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Toposort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_SimpleGroundExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_LLVMBindings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitLLVM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_ = _init_l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_);
l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_ = _init_l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_);
l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_ = _init_l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_);
l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_ = _init_l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_);
l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_ = _init_l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_);
l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_ = _init_l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_);
l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_ = _init_l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_);
l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_ = _init_l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_583794373____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_compiler_reuse = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_compiler_reuse);
lean_dec_ref(res);
}l_Lean_IR_compile___closed__0 = _init_l_Lean_IR_compile___closed__0();
lean_mark_persistent(l_Lean_IR_compile___closed__0);
l_Lean_IR_compile___closed__1 = _init_l_Lean_IR_compile___closed__1();
lean_mark_persistent(l_Lean_IR_compile___closed__1);
l_Lean_IR_compile___closed__2 = _init_l_Lean_IR_compile___closed__2();
lean_mark_persistent(l_Lean_IR_compile___closed__2);
l_Lean_IR_compile___closed__3 = _init_l_Lean_IR_compile___closed__3();
lean_mark_persistent(l_Lean_IR_compile___closed__3);
l_Lean_IR_compile___closed__4 = _init_l_Lean_IR_compile___closed__4();
lean_mark_persistent(l_Lean_IR_compile___closed__4);
l_Lean_IR_compile___closed__5 = _init_l_Lean_IR_compile___closed__5();
lean_mark_persistent(l_Lean_IR_compile___closed__5);
l_Lean_IR_compile___closed__6 = _init_l_Lean_IR_compile___closed__6();
lean_mark_persistent(l_Lean_IR_compile___closed__6);
l_Lean_IR_compile___closed__7 = _init_l_Lean_IR_compile___closed__7();
lean_mark_persistent(l_Lean_IR_compile___closed__7);
l_Lean_IR_compile___closed__8 = _init_l_Lean_IR_compile___closed__8();
lean_mark_persistent(l_Lean_IR_compile___closed__8);
l_Lean_IR_compile___closed__9 = _init_l_Lean_IR_compile___closed__9();
lean_mark_persistent(l_Lean_IR_compile___closed__9);
l_Lean_IR_compile___closed__10 = _init_l_Lean_IR_compile___closed__10();
lean_mark_persistent(l_Lean_IR_compile___closed__10);
l_Lean_IR_compile___closed__11 = _init_l_Lean_IR_compile___closed__11();
lean_mark_persistent(l_Lean_IR_compile___closed__11);
l_Lean_IR_compile___closed__12 = _init_l_Lean_IR_compile___closed__12();
lean_mark_persistent(l_Lean_IR_compile___closed__12);
l_Lean_IR_compile___closed__13 = _init_l_Lean_IR_compile___closed__13();
lean_mark_persistent(l_Lean_IR_compile___closed__13);
l_Lean_IR_compile___closed__14 = _init_l_Lean_IR_compile___closed__14();
lean_mark_persistent(l_Lean_IR_compile___closed__14);
l_Lean_IR_compile___closed__15 = _init_l_Lean_IR_compile___closed__15();
lean_mark_persistent(l_Lean_IR_compile___closed__15);
l_Lean_IR_compile___closed__16 = _init_l_Lean_IR_compile___closed__16();
lean_mark_persistent(l_Lean_IR_compile___closed__16);
l_Lean_IR_compile___closed__17 = _init_l_Lean_IR_compile___closed__17();
lean_mark_persistent(l_Lean_IR_compile___closed__17);
l_Lean_IR_compile___closed__18 = _init_l_Lean_IR_compile___closed__18();
lean_mark_persistent(l_Lean_IR_compile___closed__18);
l_Lean_IR_compile___closed__19 = _init_l_Lean_IR_compile___closed__19();
lean_mark_persistent(l_Lean_IR_compile___closed__19);
l_Lean_IR_compile___closed__20 = _init_l_Lean_IR_compile___closed__20();
lean_mark_persistent(l_Lean_IR_compile___closed__20);
l_Lean_IR_compile___closed__21 = _init_l_Lean_IR_compile___closed__21();
lean_mark_persistent(l_Lean_IR_compile___closed__21);
l_Lean_IR_compile___closed__22 = _init_l_Lean_IR_compile___closed__22();
lean_mark_persistent(l_Lean_IR_compile___closed__22);
l_Lean_IR_compile___closed__23 = _init_l_Lean_IR_compile___closed__23();
lean_mark_persistent(l_Lean_IR_compile___closed__23);
l_Lean_IR_compile___closed__24 = _init_l_Lean_IR_compile___closed__24();
lean_mark_persistent(l_Lean_IR_compile___closed__24);
l_Lean_IR_compile___closed__25 = _init_l_Lean_IR_compile___closed__25();
lean_mark_persistent(l_Lean_IR_compile___closed__25);
l_Lean_IR_compile___closed__26 = _init_l_Lean_IR_compile___closed__26();
lean_mark_persistent(l_Lean_IR_compile___closed__26);
l_Lean_IR_compile___closed__27 = _init_l_Lean_IR_compile___closed__27();
lean_mark_persistent(l_Lean_IR_compile___closed__27);
l_Lean_IR_compile___closed__28 = _init_l_Lean_IR_compile___closed__28();
lean_mark_persistent(l_Lean_IR_compile___closed__28);
l_Lean_IR_compile___closed__29 = _init_l_Lean_IR_compile___closed__29();
lean_mark_persistent(l_Lean_IR_compile___closed__29);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Compiler_IR_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_640659120____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
