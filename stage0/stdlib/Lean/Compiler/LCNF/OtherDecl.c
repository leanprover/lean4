// Lean compiler output
// Module: Lean.Compiler.LCNF.OtherDecl
// Imports: Lean.Compiler.LCNF.BaseTypes Lean.Compiler.LCNF.MonoTypes
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
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__2;
lean_object* l_Lean_Compiler_LCNF_getPhase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___closed__1;
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___closed__4;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclBaseType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___closed__3;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__3;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___closed__2;
lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__1;
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__1;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__3;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.OtherDecl", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.getOtherDeclType", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_getOtherDeclType___closed__1;
x_2 = l_Lean_Compiler_LCNF_getOtherDeclType___closed__2;
x_3 = lean_unsigned_to_nat(19u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_Compiler_LCNF_getOtherDeclType___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Compiler_LCNF_getPhase(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
switch (x_10) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_1, x_2, x_5, x_6, x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_Compiler_LCNF_getOtherDeclMonoType(x_1, x_5, x_6, x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l_Lean_Compiler_LCNF_getOtherDeclType___closed__4;
x_17 = l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1(x_16, x_3, x_4, x_5, x_6, x_15);
return x_17;
}
}
}
}
lean_object* initialize_Lean_Compiler_LCNF_BaseTypes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_OtherDecl(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_BaseTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__1);
l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__2);
l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__3 = _init_l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_getOtherDeclType___spec__1___closed__3);
l_Lean_Compiler_LCNF_getOtherDeclType___closed__1 = _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_getOtherDeclType___closed__1);
l_Lean_Compiler_LCNF_getOtherDeclType___closed__2 = _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_getOtherDeclType___closed__2);
l_Lean_Compiler_LCNF_getOtherDeclType___closed__3 = _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_getOtherDeclType___closed__3);
l_Lean_Compiler_LCNF_getOtherDeclType___closed__4 = _init_l_Lean_Compiler_LCNF_getOtherDeclType___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_getOtherDeclType___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
