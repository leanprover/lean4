// Lean compiler output
// Module: Lean.AuxRecursor
// Imports: Init Lean.Environment
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
LEAN_EXPORT lean_object* l_Lean_mkRecOnName(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150____closed__2;
LEAN_EXPORT lean_object* lean_mark_aux_recursor(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_noConfusionExt;
static lean_object* l_Lean_isAuxRecursor___closed__3;
LEAN_EXPORT uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_isAuxRecursor___closed__5;
static lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49____closed__2;
LEAN_EXPORT lean_object* l_Lean_auxRecExt;
LEAN_EXPORT lean_object* l_Lean_binductionOnSuffix;
LEAN_EXPORT uint8_t l_Lean_isBRecOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBelowName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_recOnSuffix;
LEAN_EXPORT lean_object* l_Lean_isNoConfusion___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mark_no_confusion(lean_object*, lean_object*);
static lean_object* l_Lean_markAuxRecursor___closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCasesOnRecursor___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_casesOnSuffix___closed__1;
static lean_object* l_Lean_isCasesOnRecursor___closed__1;
LEAN_EXPORT uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_markNoConfusion___closed__1;
static lean_object* l_Lean_brecOnSuffix___closed__1;
static lean_object* l_Lean_binductionOnSuffix___closed__1;
LEAN_EXPORT uint8_t lean_is_no_confusion(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
static lean_object* l_Lean_belowSuffix___closed__1;
static lean_object* l_Lean_isAuxRecursor___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkBRecOnName(lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
static lean_object* l_Lean_isAuxRecursor___closed__4;
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isBRecOnRecursor___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_isBRecOnRecursor___closed__1;
LEAN_EXPORT lean_object* l_Lean_isAuxRecursor___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150____closed__1;
LEAN_EXPORT lean_object* l_Lean_brecOnSuffix;
static lean_object* l_Lean_isAuxRecursor___closed__1;
LEAN_EXPORT lean_object* l_Lean_isAuxRecursorWithSuffix___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isAuxRecursor___closed__6;
static lean_object* l_Lean_recOnSuffix___closed__1;
LEAN_EXPORT lean_object* l_Lean_casesOnSuffix;
LEAN_EXPORT lean_object* l_Lean_mkBInductionOnName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_belowSuffix;
static lean_object* _init_l_Lean_casesOnSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("casesOn");
return x_1;
}
}
static lean_object* _init_l_Lean_casesOnSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_casesOnSuffix___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_recOnSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("recOn");
return x_1;
}
}
static lean_object* _init_l_Lean_recOnSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_recOnSuffix___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_brecOnSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOn");
return x_1;
}
}
static lean_object* _init_l_Lean_brecOnSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_brecOnSuffix___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_binductionOnSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("binductionOn");
return x_1;
}
}
static lean_object* _init_l_Lean_binductionOnSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_binductionOnSuffix___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_belowSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("below");
return x_1;
}
}
static lean_object* _init_l_Lean_belowSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_belowSuffix___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_casesOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_recOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_brecOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBInductionOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_binductionOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelowName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_belowSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("auxRec");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49____closed__2;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_markAuxRecursor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_auxRecExt;
return x_1;
}
}
LEAN_EXPORT lean_object* lean_mark_aux_recursor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_markAuxRecursor___closed__1;
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_isAuxRecursor___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ndrec");
return x_1;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_isAuxRecursor___closed__2;
x_2 = l_Lean_isAuxRecursor___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ndrecOn");
return x_1;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_isAuxRecursor___closed__2;
x_2 = l_Lean_isAuxRecursor___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_is_aux_recursor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_markAuxRecursor___closed__1;
lean_inc(x_2);
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_isAuxRecursor___closed__4;
x_6 = lean_name_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_isAuxRecursor___closed__6;
x_8 = lean_name_eq(x_2, x_7);
lean_dec(x_2);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = 1;
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_2);
x_10 = 1;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAuxRecursor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_aux_recursor(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = lean_name_mk_string(x_5, x_4);
x_7 = lean_name_eq(x_6, x_3);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_is_aux_recursor(x_1, x_2);
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAuxRecursorWithSuffix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_isAuxRecursorWithSuffix(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_isCasesOnRecursor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_casesOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_isCasesOnRecursor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_isCasesOnRecursor___closed__1;
x_4 = l_Lean_isAuxRecursorWithSuffix(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isCasesOnRecursor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isCasesOnRecursor(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_isBRecOnRecursor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_brecOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_isBRecOnRecursor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_isBRecOnRecursor___closed__1;
x_4 = l_Lean_isAuxRecursorWithSuffix(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isBRecOnRecursor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isBRecOnRecursor(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("noConf");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150____closed__2;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_markNoConfusion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_noConfusionExt;
return x_1;
}
}
LEAN_EXPORT lean_object* lean_mark_no_confusion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_markNoConfusion___closed__1;
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_is_no_confusion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_markNoConfusion___closed__1;
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isNoConfusion___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_no_confusion(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_AuxRecursor(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_casesOnSuffix___closed__1 = _init_l_Lean_casesOnSuffix___closed__1();
lean_mark_persistent(l_Lean_casesOnSuffix___closed__1);
l_Lean_casesOnSuffix = _init_l_Lean_casesOnSuffix();
lean_mark_persistent(l_Lean_casesOnSuffix);
l_Lean_recOnSuffix___closed__1 = _init_l_Lean_recOnSuffix___closed__1();
lean_mark_persistent(l_Lean_recOnSuffix___closed__1);
l_Lean_recOnSuffix = _init_l_Lean_recOnSuffix();
lean_mark_persistent(l_Lean_recOnSuffix);
l_Lean_brecOnSuffix___closed__1 = _init_l_Lean_brecOnSuffix___closed__1();
lean_mark_persistent(l_Lean_brecOnSuffix___closed__1);
l_Lean_brecOnSuffix = _init_l_Lean_brecOnSuffix();
lean_mark_persistent(l_Lean_brecOnSuffix);
l_Lean_binductionOnSuffix___closed__1 = _init_l_Lean_binductionOnSuffix___closed__1();
lean_mark_persistent(l_Lean_binductionOnSuffix___closed__1);
l_Lean_binductionOnSuffix = _init_l_Lean_binductionOnSuffix();
lean_mark_persistent(l_Lean_binductionOnSuffix);
l_Lean_belowSuffix___closed__1 = _init_l_Lean_belowSuffix___closed__1();
lean_mark_persistent(l_Lean_belowSuffix___closed__1);
l_Lean_belowSuffix = _init_l_Lean_belowSuffix();
lean_mark_persistent(l_Lean_belowSuffix);
l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49____closed__1 = _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49____closed__1);
l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49____closed__2 = _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49____closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_49_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_auxRecExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_auxRecExt);
lean_dec_ref(res);
}l_Lean_markAuxRecursor___closed__1 = _init_l_Lean_markAuxRecursor___closed__1();
lean_mark_persistent(l_Lean_markAuxRecursor___closed__1);
l_Lean_isAuxRecursor___closed__1 = _init_l_Lean_isAuxRecursor___closed__1();
lean_mark_persistent(l_Lean_isAuxRecursor___closed__1);
l_Lean_isAuxRecursor___closed__2 = _init_l_Lean_isAuxRecursor___closed__2();
lean_mark_persistent(l_Lean_isAuxRecursor___closed__2);
l_Lean_isAuxRecursor___closed__3 = _init_l_Lean_isAuxRecursor___closed__3();
lean_mark_persistent(l_Lean_isAuxRecursor___closed__3);
l_Lean_isAuxRecursor___closed__4 = _init_l_Lean_isAuxRecursor___closed__4();
lean_mark_persistent(l_Lean_isAuxRecursor___closed__4);
l_Lean_isAuxRecursor___closed__5 = _init_l_Lean_isAuxRecursor___closed__5();
lean_mark_persistent(l_Lean_isAuxRecursor___closed__5);
l_Lean_isAuxRecursor___closed__6 = _init_l_Lean_isAuxRecursor___closed__6();
lean_mark_persistent(l_Lean_isAuxRecursor___closed__6);
l_Lean_isCasesOnRecursor___closed__1 = _init_l_Lean_isCasesOnRecursor___closed__1();
lean_mark_persistent(l_Lean_isCasesOnRecursor___closed__1);
l_Lean_isBRecOnRecursor___closed__1 = _init_l_Lean_isBRecOnRecursor___closed__1();
lean_mark_persistent(l_Lean_isBRecOnRecursor___closed__1);
l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150____closed__1 = _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150____closed__1);
l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150____closed__2 = _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150____closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_150_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_noConfusionExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_noConfusionExt);
lean_dec_ref(res);
}l_Lean_markNoConfusion___closed__1 = _init_l_Lean_markNoConfusion___closed__1();
lean_mark_persistent(l_Lean_markNoConfusion___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
