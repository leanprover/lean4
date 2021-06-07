// Lean compiler output
// Module: Lean.Util.PPExt
// Imports: Init Lean.Environment Lean.Syntax Lean.MetavarContext Lean.Data.OpenDecl
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
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__5;
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__1;
static lean_object* l_Lean_ppExpr___closed__5;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_pp_raw_maxDepth___closed__1;
static lean_object* l_Lean_pp_raw___closed__1;
lean_object* l_Lean_PPContext_mctx___default;
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_ppExpr___closed__3;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_PPContext_opts___default;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_ppTerm___closed__3;
lean_object* l_Lean_PPContext_lctx___default;
lean_object* l_Lean_PPContext_openDecls___default;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__3;
static lean_object* l_Lean_instInhabitedPPFns___closed__2;
lean_object* l_Lean_pp_raw_showInfo;
lean_object* l_Std_fmt___at_Lean_ppExpr___spec__3(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__2;
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__4;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_279_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4_(lean_object*);
static uint32_t l_Lean_instInhabitedPPFns___lambda__1___closed__1;
lean_object* l_Lean_pp_raw;
lean_object* l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_mctx___default___closed__1;
uint8_t l_Lean_Option_get___at_Lean_ppTerm___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__2;
static lean_object* l_Lean_ppTerm___closed__1;
lean_object* l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_25____spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__4;
lean_object* l_Lean_ppGoal(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_mctx___default___closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__6;
static lean_object* l_Lean_ppExt___closed__1;
static lean_object* l_Lean_PPContext_mctx___default___closed__4;
lean_object* l_Lean_pp_raw_maxDepth;
lean_object* l_Std_fmt___at_Lean_ppExpr___spec__3___boxed(lean_object*);
lean_object* l_Lean_pp_rawOnError;
static lean_object* l_Lean_ppExt___closed__2;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___closed__2;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_49____spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_ppExpr___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_ppFnsRef;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ppTerm___closed__4;
static lean_object* l_Lean_PPContext_mctx___default___closed__3;
static lean_object* l_Lean_instInhabitedPPFns___closed__1;
lean_object* lean_expr_dbg_to_string(lean_object*);
static lean_object* l_Lean_PPContext_lctx___default___closed__2;
lean_object* l_Lean_ppExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__4;
lean_object* l_Lean_PPContext_currNamespace___default;
lean_object* l_Lean_Option_get___at_Lean_ppExpr___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_lctx___default___closed__1;
static lean_object* l_Lean_PPContext_lctx___default___closed__4;
lean_object* l_Lean_instInhabitedPPFns___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__4;
lean_object* l_Lean_instInhabitedPPFns;
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__2;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__1;
lean_object* l_Lean_Option_get___at_Lean_ppTerm___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___closed__1;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ppTerm___closed__2;
static lean_object* l_Lean_instInhabitedPPFns___lambda__1___closed__3;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_279____lambda__1(lean_object*);
lean_object* l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__3;
static lean_object* l_Lean_PPContext_lctx___default___closed__3;
lean_object* l_Std_fmt___at_Lean_ppExpr___spec__2(lean_object*);
static lean_object* l_Lean_ppExpr___closed__6;
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__3;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ppExpr___closed__2;
lean_object* l_Lean_ppTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__3;
lean_object* l_Lean_ppExt;
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_279____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__3;
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_Lean_ppExpr___closed__7;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_ppExpr___closed__4;
static lean_object* l_Lean_ppExpr___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__2;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedPPFns___lambda__1___closed__2;
lean_object* l_Lean_instInhabitedPPFns___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pp");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("raw");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__2;
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) print raw expression/syntax tree");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__5;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__4;
x_3 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__6;
x_4 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_49____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_pp_raw___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("showInfo");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__4;
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) print `SourceInfo` metadata with raw printer");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__4;
x_4 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_49____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maxDepth");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__4;
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) maximum `Syntax` depth for raw printer");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__4;
x_4 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_25____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_pp_raw_maxDepth___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rawOnError");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__2;
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) fallback to 'raw' printer when pretty printer fails");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__1;
x_3 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__4;
x_4 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_49____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_PPContext_mctx___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_mctx___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_mctx___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_mctx___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_mctx___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_mctx___default___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_PPContext_mctx___default___closed__3;
x_3 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_mctx___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PPContext_mctx___default___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_lctx___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_lctx___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_lctx___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_lctx___default___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_PPContext_lctx___default___closed__2;
x_3 = l_Lean_PPContext_lctx___default___closed__1;
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
static lean_object* _init_l_Lean_PPContext_lctx___default___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_mctx___default___closed__3;
x_2 = l_Lean_PPContext_lctx___default___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_lctx___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PPContext_lctx___default___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_opts___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_currNamespace___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_openDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint32_t _init_l_Lean_instInhabitedPPFns___lambda__1___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedPPFns___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedPPFns___lambda__1___closed__3() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedPPFns___lambda__1___closed__1;
x_2 = l_Lean_instInhabitedPPFns___lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Lean_instInhabitedPPFns___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_instInhabitedPPFns___lambda__1___closed__3;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_instInhabitedPPFns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instInhabitedPPFns___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedPPFns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedPPFns___closed__1;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedPPFns() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPPFns___closed__2;
return x_1;
}
}
lean_object* l_Lean_instInhabitedPPFns___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedPPFns___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 3)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
else
{
lean_dec(x_6);
lean_inc(x_4);
return x_4;
}
}
}
}
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_expr_dbg_to_string(x_2);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_pp_raw_maxDepth;
x_6 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1(x_4, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = 0;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_formatStxAux(x_7, x_8, x_9, x_2);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("goal");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___closed__2;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__4;
x_3 = l_IO_mkRef___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__2(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_279____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_ppFnsRef;
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
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_279____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_279____lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_279_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_279____closed__1;
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ppExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ppExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_ppExt___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
uint8_t l_Lean_Option_get___at_Lean_ppExpr___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
lean_object* l_Std_fmt___at_Lean_ppExpr___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_io_error_to_string(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Std_fmt___at_Lean_ppExpr___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_expr_dbg_to_string(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ppExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)");
return x_1;
}
}
static lean_object* _init_l_Lean_ppExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppExpr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ppExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[Error pretty printing expression: ");
return x_1;
}
}
static lean_object* _init_l_Lean_ppExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppExpr___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ppExpr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(". Falling back to raw printer.]");
return x_1;
}
}
static lean_object* _init_l_Lean_ppExpr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppExpr___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ppExpr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedPPFns___lambda__1___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_Lean_MetavarContext_instantiateMVars(x_4, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = l_Lean_pp_raw;
x_9 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = l_Lean_ppExt;
x_12 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_11, x_10);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_6);
x_14 = lean_apply_3(x_13, x_1, x_6, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_pp_rawOnError;
x_18 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_7, x_17);
lean_dec(x_7);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_6);
x_19 = l_Lean_ppExpr___closed__2;
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = l_Std_fmt___at_Lean_ppExpr___spec__2(x_16);
x_21 = l_Lean_ppExpr___closed__4;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_ppExpr___closed__6;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_ppExpr___closed__7;
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Std_fmt___at_Lean_ppExpr___spec__3(x_6);
lean_dec(x_6);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_31);
return x_14;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = l_Lean_pp_rawOnError;
x_35 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_7, x_34);
lean_dec(x_7);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_32);
lean_dec(x_6);
x_36 = l_Lean_ppExpr___closed__2;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = l_Std_fmt___at_Lean_ppExpr___spec__2(x_32);
x_39 = l_Lean_ppExpr___closed__4;
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_ppExpr___closed__6;
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_box(1);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_ppExpr___closed__7;
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Std_fmt___at_Lean_ppExpr___spec__3(x_6);
lean_dec(x_6);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_33);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_1);
x_51 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_3);
return x_53;
}
}
}
lean_object* l_Lean_Option_get___at_Lean_ppExpr___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Std_fmt___at_Lean_ppExpr___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_fmt___at_Lean_ppExpr___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Option_get___at_Lean_ppTerm___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
static lean_object* _init_l_Lean_ppTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)");
return x_1;
}
}
static lean_object* _init_l_Lean_ppTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppTerm___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ppTerm___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[Error pretty printing syntax: ");
return x_1;
}
}
static lean_object* _init_l_Lean_ppTerm___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppTerm___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ppTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = l_Lean_pp_raw;
x_6 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = l_Lean_ppExt;
x_9 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_2);
x_11 = lean_apply_3(x_10, x_1, x_2, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_pp_rawOnError;
x_15 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_4, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
x_16 = l_Lean_ppTerm___closed__2;
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_17 = l_Std_fmt___at_Lean_ppExpr___spec__2(x_13);
x_18 = l_Lean_ppTerm___closed__4;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_ppExpr___closed__6;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_ppExpr___closed__7;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_pp_raw_maxDepth;
x_27 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1(x_4, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_pp_raw_showInfo;
x_30 = l_Lean_Option_get___at_Lean_ppTerm___spec__1(x_4, x_29);
lean_dec(x_4);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_Syntax_formatStxAux(x_28, x_30, x_31, x_2);
lean_dec(x_28);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_34);
return x_11;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_11, 0);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_11);
x_37 = l_Lean_pp_rawOnError;
x_38 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_4, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_2);
x_39 = l_Lean_ppTerm___closed__2;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_41 = l_Std_fmt___at_Lean_ppExpr___spec__2(x_35);
x_42 = l_Lean_ppTerm___closed__4;
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_ppExpr___closed__6;
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_ppExpr___closed__7;
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_pp_raw_maxDepth;
x_51 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1(x_4, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_pp_raw_showInfo;
x_54 = l_Lean_Option_get___at_Lean_ppTerm___spec__1(x_4, x_53);
lean_dec(x_4);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Syntax_formatStxAux(x_52, x_54, x_55, x_2);
lean_dec(x_52);
x_57 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_48);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_36);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_1);
x_60 = l_Lean_pp_raw_maxDepth;
x_61 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1(x_4, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Lean_pp_raw_showInfo;
x_64 = l_Lean_Option_get___at_Lean_ppTerm___spec__1(x_4, x_63);
lean_dec(x_4);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Lean_Syntax_formatStxAux(x_62, x_64, x_65, x_2);
lean_dec(x_62);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_3);
return x_67;
}
}
}
lean_object* l_Lean_Option_get___at_Lean_ppTerm___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at_Lean_ppTerm___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_ppGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lean_ppExt;
x_6 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_5, x_4);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_3(x_7, x_1, x_2, x_3);
return x_8;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Syntax(lean_object*);
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
res = initialize_Lean_Syntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_OpenDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__1 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__1);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__2 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__2);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__3 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__3);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__4 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__4);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__5 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__5);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__6 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4____closed__6);
l_Lean_pp_raw___closed__1 = _init_l_Lean_pp_raw___closed__1();
lean_mark_persistent(l_Lean_pp_raw___closed__1);
res = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_raw = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_raw);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__1 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__1);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__2 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__2);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__3 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__3);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__4 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29____closed__4);
res = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_29_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_raw_showInfo = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_raw_showInfo);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__1 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__1);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__2 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__2);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__3 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__3);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__4 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54____closed__4);
l_Lean_pp_raw_maxDepth___closed__1 = _init_l_Lean_pp_raw_maxDepth___closed__1();
lean_mark_persistent(l_Lean_pp_raw_maxDepth___closed__1);
res = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_54_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_raw_maxDepth = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_raw_maxDepth);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__1 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__1);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__2 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__2);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__3 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__3);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__4 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79____closed__4);
res = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_79_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_rawOnError = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_rawOnError);
lean_dec_ref(res);
l_Lean_PPContext_mctx___default___closed__1 = _init_l_Lean_PPContext_mctx___default___closed__1();
lean_mark_persistent(l_Lean_PPContext_mctx___default___closed__1);
l_Lean_PPContext_mctx___default___closed__2 = _init_l_Lean_PPContext_mctx___default___closed__2();
lean_mark_persistent(l_Lean_PPContext_mctx___default___closed__2);
l_Lean_PPContext_mctx___default___closed__3 = _init_l_Lean_PPContext_mctx___default___closed__3();
lean_mark_persistent(l_Lean_PPContext_mctx___default___closed__3);
l_Lean_PPContext_mctx___default___closed__4 = _init_l_Lean_PPContext_mctx___default___closed__4();
lean_mark_persistent(l_Lean_PPContext_mctx___default___closed__4);
l_Lean_PPContext_mctx___default = _init_l_Lean_PPContext_mctx___default();
lean_mark_persistent(l_Lean_PPContext_mctx___default);
l_Lean_PPContext_lctx___default___closed__1 = _init_l_Lean_PPContext_lctx___default___closed__1();
lean_mark_persistent(l_Lean_PPContext_lctx___default___closed__1);
l_Lean_PPContext_lctx___default___closed__2 = _init_l_Lean_PPContext_lctx___default___closed__2();
lean_mark_persistent(l_Lean_PPContext_lctx___default___closed__2);
l_Lean_PPContext_lctx___default___closed__3 = _init_l_Lean_PPContext_lctx___default___closed__3();
lean_mark_persistent(l_Lean_PPContext_lctx___default___closed__3);
l_Lean_PPContext_lctx___default___closed__4 = _init_l_Lean_PPContext_lctx___default___closed__4();
lean_mark_persistent(l_Lean_PPContext_lctx___default___closed__4);
l_Lean_PPContext_lctx___default = _init_l_Lean_PPContext_lctx___default();
lean_mark_persistent(l_Lean_PPContext_lctx___default);
l_Lean_PPContext_opts___default = _init_l_Lean_PPContext_opts___default();
lean_mark_persistent(l_Lean_PPContext_opts___default);
l_Lean_PPContext_currNamespace___default = _init_l_Lean_PPContext_currNamespace___default();
lean_mark_persistent(l_Lean_PPContext_currNamespace___default);
l_Lean_PPContext_openDecls___default = _init_l_Lean_PPContext_openDecls___default();
lean_mark_persistent(l_Lean_PPContext_openDecls___default);
l_Lean_instInhabitedPPFns___lambda__1___closed__1 = _init_l_Lean_instInhabitedPPFns___lambda__1___closed__1();
l_Lean_instInhabitedPPFns___lambda__1___closed__2 = _init_l_Lean_instInhabitedPPFns___lambda__1___closed__2();
lean_mark_persistent(l_Lean_instInhabitedPPFns___lambda__1___closed__2);
l_Lean_instInhabitedPPFns___lambda__1___closed__3 = _init_l_Lean_instInhabitedPPFns___lambda__1___closed__3();
lean_mark_persistent(l_Lean_instInhabitedPPFns___lambda__1___closed__3);
l_Lean_instInhabitedPPFns___closed__1 = _init_l_Lean_instInhabitedPPFns___closed__1();
lean_mark_persistent(l_Lean_instInhabitedPPFns___closed__1);
l_Lean_instInhabitedPPFns___closed__2 = _init_l_Lean_instInhabitedPPFns___closed__2();
lean_mark_persistent(l_Lean_instInhabitedPPFns___closed__2);
l_Lean_instInhabitedPPFns = _init_l_Lean_instInhabitedPPFns();
lean_mark_persistent(l_Lean_instInhabitedPPFns);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___closed__1 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___closed__1);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___closed__2 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____lambda__3___closed__2);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__1 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__1);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__2 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__2);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__3 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__3);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__4 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____closed__4);
res = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_231_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_ppFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppFnsRef);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_279____closed__1 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_279____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_279____closed__1);
l_Lean_ppExt___closed__1 = _init_l_Lean_ppExt___closed__1();
lean_mark_persistent(l_Lean_ppExt___closed__1);
l_Lean_ppExt___closed__2 = _init_l_Lean_ppExt___closed__2();
lean_mark_persistent(l_Lean_ppExt___closed__2);
res = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_279_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_ppExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppExt);
lean_dec_ref(res);
l_Lean_ppExpr___closed__1 = _init_l_Lean_ppExpr___closed__1();
lean_mark_persistent(l_Lean_ppExpr___closed__1);
l_Lean_ppExpr___closed__2 = _init_l_Lean_ppExpr___closed__2();
lean_mark_persistent(l_Lean_ppExpr___closed__2);
l_Lean_ppExpr___closed__3 = _init_l_Lean_ppExpr___closed__3();
lean_mark_persistent(l_Lean_ppExpr___closed__3);
l_Lean_ppExpr___closed__4 = _init_l_Lean_ppExpr___closed__4();
lean_mark_persistent(l_Lean_ppExpr___closed__4);
l_Lean_ppExpr___closed__5 = _init_l_Lean_ppExpr___closed__5();
lean_mark_persistent(l_Lean_ppExpr___closed__5);
l_Lean_ppExpr___closed__6 = _init_l_Lean_ppExpr___closed__6();
lean_mark_persistent(l_Lean_ppExpr___closed__6);
l_Lean_ppExpr___closed__7 = _init_l_Lean_ppExpr___closed__7();
lean_mark_persistent(l_Lean_ppExpr___closed__7);
l_Lean_ppTerm___closed__1 = _init_l_Lean_ppTerm___closed__1();
lean_mark_persistent(l_Lean_ppTerm___closed__1);
l_Lean_ppTerm___closed__2 = _init_l_Lean_ppTerm___closed__2();
lean_mark_persistent(l_Lean_ppTerm___closed__2);
l_Lean_ppTerm___closed__3 = _init_l_Lean_ppTerm___closed__3();
lean_mark_persistent(l_Lean_ppTerm___closed__3);
l_Lean_ppTerm___closed__4 = _init_l_Lean_ppTerm___closed__4();
lean_mark_persistent(l_Lean_ppTerm___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
