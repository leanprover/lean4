// Lean compiler output
// Module: Lean.AuxRecursor
// Imports: Lean.Environment
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
LEAN_EXPORT lean_object* l_Lean_mkIBelowName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBelowName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isNoConfusion___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAuxRecursorWithSuffix___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_markNoConfusion___closed__1;
static lean_object* l_Lean_isAuxRecursorWithSuffix___closed__1;
LEAN_EXPORT lean_object* l_Lean_ibelowSuffix;
LEAN_EXPORT lean_object* l_Lean_casesOnSuffix;
LEAN_EXPORT lean_object* l_Lean_markAuxRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_auxRecExt;
static lean_object* l_Lean_belowSuffix___closed__1;
static lean_object* l_Lean_isAuxRecursor___closed__5;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnName(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_binductionOnSuffix;
static lean_object* l_Lean_isAuxRecursorWithSuffix___closed__2;
static lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__3;
LEAN_EXPORT lean_object* l_Lean_mkRecOnName(lean_object*);
LEAN_EXPORT uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
static lean_object* l_Lean_binductionOnSuffix___closed__1;
LEAN_EXPORT uint8_t lean_is_no_confusion(lean_object*, lean_object*);
static lean_object* l_Lean_brecOnSuffix___closed__1;
LEAN_EXPORT lean_object* l_Lean_isRecOnRecursor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBRecOnName(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213____closed__2;
static lean_object* l_Lean_recOnSuffix___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213____closed__1;
LEAN_EXPORT lean_object* l_Lean_belowSuffix;
static lean_object* l_Lean_isAuxRecursor___closed__2;
LEAN_EXPORT lean_object* l_Lean_recOnSuffix;
static lean_object* l_Lean_isAuxRecursor___closed__3;
static lean_object* l_Lean_casesOnSuffix___closed__1;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isAuxRecursor___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkBInductionOnName(lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_brecOnSuffix;
static lean_object* l_Lean_ibelowSuffix___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isBRecOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCasesOnRecursor___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isRecOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isBRecOnRecursor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_markNoConfusion(lean_object*, lean_object*);
static lean_object* l_Lean_isAuxRecursor___closed__4;
static lean_object* l_Lean_markAuxRecursor___closed__1;
LEAN_EXPORT lean_object* l_Lean_noConfusionExt;
uint8_t l_Substring_beq(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAuxRecursor___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
static lean_object* _init_l_Lean_casesOnSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("casesOn", 7, 7);
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
x_1 = lean_mk_string_unchecked("recOn", 5, 5);
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
x_1 = lean_mk_string_unchecked("brecOn", 6, 6);
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
x_1 = lean_mk_string_unchecked("binductionOn", 12, 12);
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
x_1 = lean_mk_string_unchecked("below", 5, 5);
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
static lean_object* _init_l_Lean_ibelowSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ibelow", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_ibelowSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ibelowSuffix___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_casesOnSuffix;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_recOnSuffix;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_brecOnSuffix;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBInductionOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_binductionOnSuffix;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelowName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_belowSuffix;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIBelowName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_ibelowSuffix;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("auxRecExt", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__1;
x_2 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__3;
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
LEAN_EXPORT lean_object* l_Lean_markAuxRecursor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_markAuxRecursor___closed__1;
x_4 = l_Lean_TagDeclarationExtension_tag(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ndrec", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_isAuxRecursor___closed__1;
x_2 = l_Lean_isAuxRecursor___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ndrecOn", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_isAuxRecursor___closed__1;
x_2 = l_Lean_isAuxRecursor___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
lean_dec(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_isAuxRecursor___closed__3;
x_6 = lean_name_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_isAuxRecursor___closed__5;
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
static lean_object* _init_l_Lean_isAuxRecursorWithSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_isAuxRecursorWithSuffix___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_string_dec_eq(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_6 = l_Lean_isAuxRecursorWithSuffix___closed__1;
x_7 = lean_string_append(x_6, x_3);
x_8 = l_Lean_isAuxRecursorWithSuffix___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_utf8_byte_size(x_4);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_10);
x_13 = lean_string_length(x_9);
x_14 = l_Substring_nextn(x_12, x_13, x_11);
lean_dec(x_12);
x_15 = lean_nat_add(x_11, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_string_utf8_byte_size(x_9);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Substring_beq(x_16, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_is_aux_recursor(x_1, x_2);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_4);
x_22 = lean_is_aux_recursor(x_1, x_2);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = 0;
return x_23;
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
LEAN_EXPORT uint8_t l_Lean_isCasesOnRecursor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_casesOnSuffix;
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
LEAN_EXPORT uint8_t l_Lean_isRecOnRecursor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_recOnSuffix;
x_4 = l_Lean_isAuxRecursorWithSuffix(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isRecOnRecursor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isRecOnRecursor(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isBRecOnRecursor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_brecOnSuffix;
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
static lean_object* _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("noConfusionExt", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__1;
x_2 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213____closed__2;
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
LEAN_EXPORT lean_object* l_Lean_markNoConfusion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_markNoConfusion___closed__1;
x_4 = l_Lean_TagDeclarationExtension_tag(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_is_no_confusion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_markNoConfusion___closed__1;
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
lean_dec(x_1);
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
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_AuxRecursor(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
l_Lean_ibelowSuffix___closed__1 = _init_l_Lean_ibelowSuffix___closed__1();
lean_mark_persistent(l_Lean_ibelowSuffix___closed__1);
l_Lean_ibelowSuffix = _init_l_Lean_ibelowSuffix();
lean_mark_persistent(l_Lean_ibelowSuffix);
l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__1 = _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__1);
l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__2 = _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__2);
l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__3 = _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_70_(lean_io_mk_world());
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
l_Lean_isAuxRecursorWithSuffix___closed__1 = _init_l_Lean_isAuxRecursorWithSuffix___closed__1();
lean_mark_persistent(l_Lean_isAuxRecursorWithSuffix___closed__1);
l_Lean_isAuxRecursorWithSuffix___closed__2 = _init_l_Lean_isAuxRecursorWithSuffix___closed__2();
lean_mark_persistent(l_Lean_isAuxRecursorWithSuffix___closed__2);
l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213____closed__1 = _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213____closed__1);
l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213____closed__2 = _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213____closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_213_(lean_io_mk_world());
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
