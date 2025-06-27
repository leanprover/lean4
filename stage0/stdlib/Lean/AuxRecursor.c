// Lean compiler output
// Module: Lean.AuxRecursor
// Imports: Lean.EnvExtension
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
LEAN_EXPORT lean_object* l_Lean_mkBelowName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isNoConfusion___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAuxRecursorWithSuffix___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_markNoConfusion___closed__0;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_AuxRecursor___hyg_47_;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_AuxRecursor___hyg_189_;
LEAN_EXPORT lean_object* l_Lean_casesOnSuffix;
LEAN_EXPORT lean_object* l_Lean_markAuxRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_auxRecExt;
static lean_object* l_Lean_recOnSuffix___closed__0;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnName(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRecOnName(lean_object*);
LEAN_EXPORT uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_AuxRecursor___hyg_189_;
static lean_object* l_Lean_brecOnSuffix___closed__0;
LEAN_EXPORT uint8_t lean_is_no_confusion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRecOnRecursor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBRecOnName(lean_object*);
static lean_object* l_Lean_casesOnSuffix___closed__0;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_belowSuffix;
static lean_object* l_Lean_isAuxRecursor___closed__2;
LEAN_EXPORT lean_object* l_Lean_recOnSuffix;
static lean_object* l_Lean_isAuxRecursor___closed__3;
static lean_object* l_Lean_isAuxRecursorWithSuffix___closed__0;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isAuxRecursor___closed__1;
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_brecOnSuffix;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_AuxRecursor___hyg_47_;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_isAuxRecursor___closed__0;
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isBRecOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCasesOnRecursor___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isRecOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isBRecOnRecursor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_markNoConfusion(lean_object*, lean_object*);
static lean_object* l_Lean_isAuxRecursor___closed__4;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_47_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_189_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_noConfusionExt;
uint8_t l_Substring_beq(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_AuxRecursor___hyg_47_;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isAuxRecursorWithSuffix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAuxRecursor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
static lean_object* l_Lean_belowSuffix___closed__0;
static lean_object* l_Lean_markAuxRecursor___closed__0;
static lean_object* _init_l_Lean_casesOnSuffix___closed__0() {
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
x_1 = l_Lean_casesOnSuffix___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_recOnSuffix___closed__0() {
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
x_1 = l_Lean_recOnSuffix___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_brecOnSuffix___closed__0() {
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
x_1 = l_Lean_brecOnSuffix___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_belowSuffix___closed__0() {
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
x_1 = l_Lean_belowSuffix___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_casesOnSuffix___closed__0;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_recOnSuffix___closed__0;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_brecOnSuffix___closed__0;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelowName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_belowSuffix___closed__0;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_AuxRecursor___hyg_47_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_AuxRecursor___hyg_47_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("auxRecExt", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_AuxRecursor___hyg_47_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_AuxRecursor___hyg_47_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_AuxRecursor___hyg_47_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_47_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__2____x40_Lean_AuxRecursor___hyg_47_;
x_3 = lean_box(2);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_mkTagDeclarationExtension(x_2, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_markAuxRecursor___closed__0() {
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
x_3 = l_Lean_markAuxRecursor___closed__0;
x_4 = l_Lean_TagDeclarationExtension_tag(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ndrecOn", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_isAuxRecursor___closed__1;
x_2 = l_Lean_isAuxRecursor___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ndrec", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_isAuxRecursor___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_isAuxRecursor___closed__3;
x_2 = l_Lean_isAuxRecursor___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_is_aux_recursor(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_markAuxRecursor___closed__0;
lean_inc(x_2);
x_8 = l_Lean_TagDeclarationExtension_isTagged(x_7, x_1, x_2);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_isAuxRecursor___closed__4;
x_10 = lean_name_eq(x_2, x_9);
x_3 = x_10;
goto block_6;
}
else
{
x_3 = x_8;
goto block_6;
}
block_6:
{
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_isAuxRecursor___closed__2;
x_5 = lean_name_eq(x_2, x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_dec(x_2);
return x_3;
}
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
static lean_object* _init_l_Lean_isAuxRecursorWithSuffix___closed__0() {
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
uint8_t x_4; 
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_string_dec_eq(x_7, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_9 = l_Lean_isAuxRecursorWithSuffix___closed__0;
x_10 = lean_string_append(x_3, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_byte_size(x_7);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_string_length(x_10);
x_15 = l_Substring_nextn(x_13, x_14, x_11);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_string_utf8_byte_size(x_10);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Substring_beq(x_16, x_18);
x_4 = x_19;
goto block_6;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
x_4 = x_8;
goto block_6;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
return x_21;
}
block_6:
{
if (x_4 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = lean_is_aux_recursor(x_1, x_2);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAuxRecursorWithSuffix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_isAuxRecursorWithSuffix(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_isCasesOnRecursor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_casesOnSuffix___closed__0;
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
x_3 = l_Lean_recOnSuffix___closed__0;
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
x_3 = l_Lean_brecOnSuffix___closed__0;
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
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_AuxRecursor___hyg_189_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("noConfusionExt", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_AuxRecursor___hyg_189_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_AuxRecursor___hyg_189_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_AuxRecursor___hyg_47_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_189_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_AuxRecursor___hyg_189_;
x_3 = lean_box(2);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_mkTagDeclarationExtension(x_2, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_markNoConfusion___closed__0() {
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
x_3 = l_Lean_markNoConfusion___closed__0;
x_4 = l_Lean_TagDeclarationExtension_tag(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_is_no_confusion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_markNoConfusion___closed__0;
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
lean_object* initialize_Lean_EnvExtension(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_AuxRecursor(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_casesOnSuffix___closed__0 = _init_l_Lean_casesOnSuffix___closed__0();
lean_mark_persistent(l_Lean_casesOnSuffix___closed__0);
l_Lean_casesOnSuffix = _init_l_Lean_casesOnSuffix();
lean_mark_persistent(l_Lean_casesOnSuffix);
l_Lean_recOnSuffix___closed__0 = _init_l_Lean_recOnSuffix___closed__0();
lean_mark_persistent(l_Lean_recOnSuffix___closed__0);
l_Lean_recOnSuffix = _init_l_Lean_recOnSuffix();
lean_mark_persistent(l_Lean_recOnSuffix);
l_Lean_brecOnSuffix___closed__0 = _init_l_Lean_brecOnSuffix___closed__0();
lean_mark_persistent(l_Lean_brecOnSuffix___closed__0);
l_Lean_brecOnSuffix = _init_l_Lean_brecOnSuffix();
lean_mark_persistent(l_Lean_brecOnSuffix);
l_Lean_belowSuffix___closed__0 = _init_l_Lean_belowSuffix___closed__0();
lean_mark_persistent(l_Lean_belowSuffix___closed__0);
l_Lean_belowSuffix = _init_l_Lean_belowSuffix();
lean_mark_persistent(l_Lean_belowSuffix);
l_Lean_initFn___closed__0____x40_Lean_AuxRecursor___hyg_47_ = _init_l_Lean_initFn___closed__0____x40_Lean_AuxRecursor___hyg_47_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_AuxRecursor___hyg_47_);
l_Lean_initFn___closed__1____x40_Lean_AuxRecursor___hyg_47_ = _init_l_Lean_initFn___closed__1____x40_Lean_AuxRecursor___hyg_47_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_AuxRecursor___hyg_47_);
l_Lean_initFn___closed__2____x40_Lean_AuxRecursor___hyg_47_ = _init_l_Lean_initFn___closed__2____x40_Lean_AuxRecursor___hyg_47_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_AuxRecursor___hyg_47_);
if (builtin) {res = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_47_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_auxRecExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_auxRecExt);
lean_dec_ref(res);
}l_Lean_markAuxRecursor___closed__0 = _init_l_Lean_markAuxRecursor___closed__0();
lean_mark_persistent(l_Lean_markAuxRecursor___closed__0);
l_Lean_isAuxRecursor___closed__0 = _init_l_Lean_isAuxRecursor___closed__0();
lean_mark_persistent(l_Lean_isAuxRecursor___closed__0);
l_Lean_isAuxRecursor___closed__1 = _init_l_Lean_isAuxRecursor___closed__1();
lean_mark_persistent(l_Lean_isAuxRecursor___closed__1);
l_Lean_isAuxRecursor___closed__2 = _init_l_Lean_isAuxRecursor___closed__2();
lean_mark_persistent(l_Lean_isAuxRecursor___closed__2);
l_Lean_isAuxRecursor___closed__3 = _init_l_Lean_isAuxRecursor___closed__3();
lean_mark_persistent(l_Lean_isAuxRecursor___closed__3);
l_Lean_isAuxRecursor___closed__4 = _init_l_Lean_isAuxRecursor___closed__4();
lean_mark_persistent(l_Lean_isAuxRecursor___closed__4);
l_Lean_isAuxRecursorWithSuffix___closed__0 = _init_l_Lean_isAuxRecursorWithSuffix___closed__0();
lean_mark_persistent(l_Lean_isAuxRecursorWithSuffix___closed__0);
l_Lean_initFn___closed__0____x40_Lean_AuxRecursor___hyg_189_ = _init_l_Lean_initFn___closed__0____x40_Lean_AuxRecursor___hyg_189_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_AuxRecursor___hyg_189_);
l_Lean_initFn___closed__1____x40_Lean_AuxRecursor___hyg_189_ = _init_l_Lean_initFn___closed__1____x40_Lean_AuxRecursor___hyg_189_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_AuxRecursor___hyg_189_);
if (builtin) {res = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_189_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_noConfusionExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_noConfusionExt);
lean_dec_ref(res);
}l_Lean_markNoConfusion___closed__0 = _init_l_Lean_markNoConfusion___closed__0();
lean_mark_persistent(l_Lean_markNoConfusion___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
