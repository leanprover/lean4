// Lean compiler output
// Module: Lean.Elab.DeclarationRange
// Imports: Init Lean.Log Lean.Parser.Command Lean.DeclarationRange Lean.Data.Lsp.PositionEncodingKind Lean.Data.Lsp.PositionEncoding
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
lean_object* l_Lean_addDeclarationRanges___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationSelectionRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_addDeclarationRanges___rarg___closed__2;
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__2;
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges(lean_object*);
static lean_object* l_Lean_Elab_addDeclarationRanges___rarg___closed__1;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__3;
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = l_Lean_Syntax_getPos_x3f(x_1, x_4);
x_6 = l_Lean_Syntax_getTailPos_x3f(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_FileMap_toPosition(x_3, x_9);
lean_inc(x_10);
x_11 = l_Lean_FileMap_leanPosToLspPos(x_3, x_10);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set(x_12, 3, x_11);
x_13 = lean_apply_2(x_8, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = l_Lean_FileMap_toPosition(x_3, x_14);
lean_dec(x_14);
lean_inc(x_15);
x_16 = l_Lean_FileMap_leanPosToLspPos(x_3, x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_apply_2(x_8, lean_box(0), x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_5, 0);
lean_inc(x_21);
lean_dec(x_5);
x_22 = l_Lean_FileMap_toPosition(x_3, x_21);
lean_dec(x_21);
lean_inc(x_22);
x_23 = l_Lean_FileMap_leanPosToLspPos(x_3, x_22);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_inc(x_23);
lean_inc(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
x_25 = lean_apply_2(x_20, lean_box(0), x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
lean_dec(x_6);
x_27 = l_Lean_FileMap_toPosition(x_3, x_26);
lean_dec(x_26);
lean_inc(x_27);
x_28 = l_Lean_FileMap_leanPosToLspPos(x_3, x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_apply_2(x_20, lean_box(0), x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getDeclarationRange___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getDeclarationRange___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getDeclarationRange___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("instance", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_getDeclarationSelectionRef___closed__1;
x_2 = l_Lean_Elab_getDeclarationSelectionRef___closed__2;
x_3 = l_Lean_Elab_getDeclarationSelectionRef___closed__3;
x_4 = l_Lean_Elab_getDeclarationSelectionRef___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationSelectionRef(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_getDeclarationSelectionRef___closed__5;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_5, x_6);
x_8 = l_Lean_Syntax_isIdent(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = l_Lean_Syntax_isIdent(x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = l_Lean_Syntax_getArg(x_1, x_6);
lean_dec(x_1);
return x_10;
}
else
{
lean_dec(x_1);
return x_5;
}
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_12, x_14);
lean_dec(x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_addDeclarationRanges___rarg(x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Elab_getDeclarationSelectionRef(x_1);
x_9 = l_Lean_Elab_getDeclarationRange___rarg(x_2, x_3, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRanges___rarg___lambda__1), 4, 3);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_addDeclarationRanges___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("example", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addDeclarationRanges___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_getDeclarationSelectionRef___closed__1;
x_2 = l_Lean_Elab_getDeclarationSelectionRef___closed__2;
x_3 = l_Lean_Elab_getDeclarationSelectionRef___closed__3;
x_4 = l_Lean_Elab_addDeclarationRanges___rarg___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_5);
x_6 = l_Lean_Syntax_getKind(x_5);
x_7 = l_Lean_Elab_addDeclarationRanges___rarg___closed__2;
x_8 = lean_name_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_Elab_getDeclarationRange___rarg(x_1, x_3, x_5);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRanges___rarg___lambda__2), 7, 6);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_4);
lean_closure_set(x_11, 5, x_9);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRanges___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Elab_getDeclarationRange___rarg(x_1, x_2, x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRanges___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Elab_getDeclarationRange___rarg(x_1, x_3, x_5);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_addAuxDeclarationRanges___rarg___lambda__1), 7, 6);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_6);
lean_closure_set(x_9, 3, x_2);
lean_closure_set(x_9, 4, x_4);
lean_closure_set(x_9, 5, x_7);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_addAuxDeclarationRanges___rarg), 6, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DeclarationRange(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_PositionEncodingKind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_PositionEncoding(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_PositionEncodingKind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_PositionEncoding(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_getDeclarationSelectionRef___closed__1 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__1();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__1);
l_Lean_Elab_getDeclarationSelectionRef___closed__2 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__2();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__2);
l_Lean_Elab_getDeclarationSelectionRef___closed__3 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__3();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__3);
l_Lean_Elab_getDeclarationSelectionRef___closed__4 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__4();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__4);
l_Lean_Elab_getDeclarationSelectionRef___closed__5 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__5();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__5);
l_Lean_Elab_addDeclarationRanges___rarg___closed__1 = _init_l_Lean_Elab_addDeclarationRanges___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_addDeclarationRanges___rarg___closed__1);
l_Lean_Elab_addDeclarationRanges___rarg___closed__2 = _init_l_Lean_Elab_addDeclarationRanges___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_addDeclarationRanges___rarg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
