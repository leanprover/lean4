// Lean compiler output
// Module: Lean.Util.PPExt
// Imports: Init Lean.Environment Lean.MetavarContext Lean.Data.OpenDecl
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
lean_object* l_Lean_mkPPExprFnRef___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_verboseOption___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_mkPPExprFnExtension(lean_object*);
lean_object* l_Lean_mkPPExprFnExtension___closed__1;
lean_object* l_Lean_ppExprFnRef;
lean_object* l_Lean_mkPPExprFnRef___closed__1;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_IO_mkRef___at_Lean_mkPPExprFnRef___spec__1(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_ppExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppOldOption___closed__2;
extern lean_object* l_Lean_EnvExtensionInterfaceUnsafe_Ext_inhabitedExt___closed__2;
lean_object* l_Lean_mkPPExprFnRef(lean_object*);
lean_object* l_Lean_ppOld___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppOldOption___closed__1;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppExpr___closed__2;
lean_object* l_Lean_ppOldOption(lean_object*);
lean_object* lean_pp_expr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppExprExt;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(lean_object*, lean_object*);
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
lean_object* l_Lean_mkPPExprFnRef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_pp_expr(x_4, x_5, x_6, x_7, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
lean_object* _init_l_Lean_mkPPExprFnRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkPPExprFnRef___lambda__1), 3, 0);
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
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_2, x_1);
return x_3;
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
lean_object* l_Lean_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_Lean_MetavarContext_instantiateMVars(x_4, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = l_Lean_ppExpr___closed__2;
x_9 = 1;
x_10 = l_Lean_KVMap_getBool(x_7, x_8, x_9);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_11 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = l_Lean_ppExprExt;
x_16 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_15, x_14);
lean_dec(x_14);
x_17 = lean_apply_3(x_16, x_1, x_6, x_3);
return x_17;
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
lean_object* initialize_Lean_Data_OpenDecl(lean_object*);
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
res = initialize_Lean_Data_OpenDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_mkPPExprFnRef___closed__1 = _init_l_Lean_mkPPExprFnRef___closed__1();
lean_mark_persistent(l_Lean_mkPPExprFnRef___closed__1);
res = l_Lean_mkPPExprFnRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_ppExprFnRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppExprFnRef);
lean_dec_ref(res);
l_Lean_mkPPExprFnExtension___closed__1 = _init_l_Lean_mkPPExprFnExtension___closed__1();
lean_mark_persistent(l_Lean_mkPPExprFnExtension___closed__1);
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
