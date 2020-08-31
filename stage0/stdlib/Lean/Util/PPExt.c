// Lean compiler output
// Module: Lean.Util.PPExt
// Imports: Init Lean.Environment Lean.MetavarContext
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
lean_object* l_Lean_mkPPExprFnExtension___lambda__1(lean_object*);
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
extern lean_object* l_Lean_verboseOption___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_ppExprExt___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPPExprFnExtension(lean_object*);
lean_object* l_Lean_mkPPExprFnExtension___closed__1;
lean_object* l_Lean_ppExprFnRef;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_mkPPExprFnRef___closed__1;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ppExprExt___closed__3;
lean_object* l_Lean_ppExprExt___elambda__2(lean_object*);
lean_object* l_IO_mkRef___at_Lean_mkPPExprFnRef___spec__1(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_IO_Error_Inhabited___closed__1;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppExprExt___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppExprExt___closed__2;
lean_object* l_Lean_ppOldOption___closed__2;
extern lean_object* l___private_Lean_Environment_5__envExtensionsRef;
lean_object* l_Lean_mkPPExprFnRef(lean_object*);
lean_object* l_Lean_ppOld___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_ppOldOption___closed__1;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_ppExpr___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppOldOption(lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_pp_expr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_Lean_EnvExtension_getStateUnsafe___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ppExprExt___closed__1;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___closed__1;
lean_object* l_Lean_ppExprExt;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppExpr___closed__1;
lean_object* l_Lean_ppOld___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_pp_expr(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_IO_mkRef___at_Lean_mkPPExprFnRef___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* _init_l_Lean_mkPPExprFnRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppOld___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_mkPPExprFnRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkPPExprFnRef___closed__1;
x_3 = l_IO_mkRef___at_Lean_mkPPExprFnRef___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Lean_Environment_5__envExtensionsRef;
x_14 = lean_st_ref_get(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
lean_dec(x_15);
x_18 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___closed__1;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_st_ref_take(x_13, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_19);
x_23 = x_19;
x_24 = lean_array_push(x_21, x_23);
x_25 = lean_st_ref_set(x_13, x_24, x_22);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_19);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
return x_3;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_3);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_mkPPExprFnExtension___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_ppExprFnRef;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* _init_l_Lean_mkPPExprFnExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkPPExprFnExtension___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_mkPPExprFnExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkPPExprFnExtension___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_ppExprExt___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
lean_object* l_Lean_ppExprExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_Error_Inhabited___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_ppExprExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppExprExt___elambda__2), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_ppExprExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ppExprExt___elambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_ppExprExt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_ppExprExt___closed__1;
x_3 = l_Lean_ppExprExt___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_ppExprExt___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ppExprExt___elambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_ppExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ppOld");
return x_1;
}
}
lean_object* _init_l_Lean_ppExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_ppExpr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
lean_inc(x_2);
x_6 = l_Lean_MetavarContext_instantiateMVars(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_ppExpr___closed__2;
x_9 = 1;
x_10 = l_Lean_KVMap_getBool(x_4, x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_expr_dbg_to_string(x_7);
lean_dec(x_7);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_ppExprExt;
x_14 = l_Lean_EnvExtension_getStateUnsafe___rarg(x_13, x_1);
x_15 = lean_apply_5(x_14, x_1, x_2, x_3, x_4, x_7);
return x_15;
}
}
}
lean_object* _init_l_Lean_ppOldOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("disable/enable old pretty printer");
return x_1;
}
}
lean_object* _init_l_Lean_ppOldOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_verboseOption___closed__3;
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_ppOldOption___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_ppOldOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_ppExpr___closed__2;
x_3 = l_Lean_ppOldOption___closed__2;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_MetavarContext(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_PPExt(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_mkPPExprFnRef___closed__1 = _init_l_Lean_mkPPExprFnRef___closed__1();
lean_mark_persistent(l_Lean_mkPPExprFnRef___closed__1);
res = l_Lean_mkPPExprFnRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_ppExprFnRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppExprFnRef);
lean_dec_ref(res);
l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___closed__1();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_mkPPExprFnExtension___spec__1___closed__1);
l_Lean_mkPPExprFnExtension___closed__1 = _init_l_Lean_mkPPExprFnExtension___closed__1();
lean_mark_persistent(l_Lean_mkPPExprFnExtension___closed__1);
l_Lean_ppExprExt___closed__1 = _init_l_Lean_ppExprExt___closed__1();
lean_mark_persistent(l_Lean_ppExprExt___closed__1);
l_Lean_ppExprExt___closed__2 = _init_l_Lean_ppExprExt___closed__2();
lean_mark_persistent(l_Lean_ppExprExt___closed__2);
l_Lean_ppExprExt___closed__3 = _init_l_Lean_ppExprExt___closed__3();
lean_mark_persistent(l_Lean_ppExprExt___closed__3);
res = l_Lean_mkPPExprFnExtension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_ppExprExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppExprExt);
lean_dec_ref(res);
l_Lean_ppExpr___closed__1 = _init_l_Lean_ppExpr___closed__1();
lean_mark_persistent(l_Lean_ppExpr___closed__1);
l_Lean_ppExpr___closed__2 = _init_l_Lean_ppExpr___closed__2();
lean_mark_persistent(l_Lean_ppExpr___closed__2);
l_Lean_ppOldOption___closed__1 = _init_l_Lean_ppOldOption___closed__1();
lean_mark_persistent(l_Lean_ppOldOption___closed__1);
l_Lean_ppOldOption___closed__2 = _init_l_Lean_ppOldOption___closed__2();
lean_mark_persistent(l_Lean_ppOldOption___closed__2);
res = l_Lean_ppOldOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
