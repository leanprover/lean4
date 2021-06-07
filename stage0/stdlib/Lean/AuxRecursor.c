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
lean_object* l_Lean_mkRecOnName(lean_object*);
lean_object* l_Lean_noConfusionExt___elambda__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__1;
lean_object* lean_mark_aux_recursor(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt;
lean_object* l_Lean_noConfusionExt___elambda__2___boxed(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_noConfusionExt___closed__5;
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_auxRecExt___elambda__1___boxed(lean_object*);
lean_object* l_Lean_noConfusionExt___closed__3;
lean_object* l_Lean_auxRecExt___elambda__4(lean_object*, lean_object*);
lean_object* l_Lean_auxRecExt;
lean_object* l_Lean_binductionOnSuffix;
lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__2;
lean_object* l_Lean_auxRecExt___closed__4;
lean_object* l_Lean_noConfusionExt___closed__1;
lean_object* l_Lean_auxRecExt___closed__1;
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_auxRecExt___elambda__4___rarg(lean_object*);
lean_object* l_Lean_recOnSuffix;
lean_object* l_Lean_isNoConfusion___boxed(lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt___closed__2;
lean_object* l_Lean_auxRecExt___closed__2;
lean_object* lean_mark_no_confusion(lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt___elambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_auxRecExt___elambda__1(lean_object*);
extern lean_object* l_IO_instInhabitedError___closed__1;
lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101_(lean_object*);
lean_object* l_Lean_isCasesOnRecursor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_casesOnSuffix___closed__1;
lean_object* l_Lean_noConfusionExt___closed__4;
lean_object* l_Lean_isCasesOnRecursor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_auxRecExt___elambda__3(lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt___elambda__3(lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt___elambda__1___boxed(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt___elambda__4___rarg(lean_object*);
lean_object* l_Lean_brecOnSuffix___closed__1;
lean_object* l_Lean_binductionOnSuffix___closed__1;
lean_object* l_Lean_auxRecExt___elambda__2___boxed(lean_object*);
lean_object* l_Lean_auxRecExt___closed__5;
lean_object* l_Lean_auxRecExt___closed__3;
uint8_t lean_is_no_confusion(lean_object*, lean_object*);
lean_object* l_Lean_noConfusionExt___elambda__1(lean_object*);
extern lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
lean_object* l_Lean_auxRecExt___elambda__3___boxed(lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
lean_object* l_Lean_auxRecExt___elambda__2(lean_object*);
lean_object* l_Lean_noConfusionExt___elambda__4(lean_object*, lean_object*);
lean_object* l_Lean_mkBRecOnName(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__1;
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
lean_object* l_Lean_isCasesOnRecursor_match__1(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isAuxRecursor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_brecOnSuffix;
lean_object* l_Lean_auxRecExt___elambda__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_recOnSuffix___closed__1;
lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__2;
lean_object* l_Lean_noConfusionExt___elambda__2(lean_object*);
lean_object* l_Lean_casesOnSuffix;
lean_object* l_Lean_mkBInductionOnName(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
#define _init_l_Lean_casesOnSuffix___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("casesOn");\
__INIT_VAR__ = x_1; goto l_Lean_casesOnSuffix___closed__1_end;\
}\
l_Lean_casesOnSuffix___closed__1_end: ((void) 0);}
#define _init_l_Lean_casesOnSuffix(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_casesOnSuffix___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_casesOnSuffix_end;\
}\
l_Lean_casesOnSuffix_end: ((void) 0);}
#define _init_l_Lean_recOnSuffix___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("recOn");\
__INIT_VAR__ = x_1; goto l_Lean_recOnSuffix___closed__1_end;\
}\
l_Lean_recOnSuffix___closed__1_end: ((void) 0);}
#define _init_l_Lean_recOnSuffix(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_recOnSuffix___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_recOnSuffix_end;\
}\
l_Lean_recOnSuffix_end: ((void) 0);}
#define _init_l_Lean_brecOnSuffix___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("brecOn");\
__INIT_VAR__ = x_1; goto l_Lean_brecOnSuffix___closed__1_end;\
}\
l_Lean_brecOnSuffix___closed__1_end: ((void) 0);}
#define _init_l_Lean_brecOnSuffix(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_brecOnSuffix___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_brecOnSuffix_end;\
}\
l_Lean_brecOnSuffix_end: ((void) 0);}
#define _init_l_Lean_binductionOnSuffix___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("binductionOn");\
__INIT_VAR__ = x_1; goto l_Lean_binductionOnSuffix___closed__1_end;\
}\
l_Lean_binductionOnSuffix___closed__1_end: ((void) 0);}
#define _init_l_Lean_binductionOnSuffix(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_binductionOnSuffix___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_binductionOnSuffix_end;\
}\
l_Lean_binductionOnSuffix_end: ((void) 0);}
lean_object* l_Lean_mkCasesOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_casesOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkRecOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_recOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkBRecOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_brecOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkBInductionOnName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_binductionOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
#define _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("auxRec");\
__INIT_VAR__ = x_1; goto l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__1_end;\
}\
l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__1_end: ((void) 0);}
#define _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__2_end;\
}\
l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__2_end: ((void) 0);}
lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__2;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_auxRecExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_auxRecExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_auxRecExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_auxRecExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_instInhabitedError___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_auxRecExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_auxRecExt___elambda__4___rarg), 1, 0);
return x_3;
}
}
#define _init_l_Lean_auxRecExt___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_auxRecExt___elambda__4___boxed), 2, 0);\
__INIT_VAR__ = x_1; goto l_Lean_auxRecExt___closed__1_end;\
}\
l_Lean_auxRecExt___closed__1_end: ((void) 0);}
#define _init_l_Lean_auxRecExt___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_auxRecExt___elambda__3___boxed), 2, 0);\
__INIT_VAR__ = x_1; goto l_Lean_auxRecExt___closed__2_end;\
}\
l_Lean_auxRecExt___closed__2_end: ((void) 0);}
#define _init_l_Lean_auxRecExt___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_auxRecExt___elambda__2___boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_auxRecExt___closed__3_end;\
}\
l_Lean_auxRecExt___closed__3_end: ((void) 0);}
#define _init_l_Lean_auxRecExt___closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_auxRecExt___elambda__1___boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_auxRecExt___closed__4_end;\
}\
l_Lean_auxRecExt___closed__4_end: ((void) 0);}
#define _init_l_Lean_auxRecExt___closed__5(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; \
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;\
x_2 = lean_box(0);\
x_3 = l_Lean_auxRecExt___closed__1;\
x_4 = l_Lean_auxRecExt___closed__2;\
x_5 = l_Lean_auxRecExt___closed__3;\
x_6 = l_Lean_auxRecExt___closed__4;\
x_7 = lean_alloc_ctor(0, 6, 0);\
lean_ctor_set(x_7, 0, x_1);\
lean_ctor_set(x_7, 1, x_2);\
lean_ctor_set(x_7, 2, x_3);\
lean_ctor_set(x_7, 3, x_4);\
lean_ctor_set(x_7, 4, x_5);\
lean_ctor_set(x_7, 5, x_6);\
__INIT_VAR__ = x_7; goto l_Lean_auxRecExt___closed__5_end;\
}\
l_Lean_auxRecExt___closed__5_end: ((void) 0);}
lean_object* l_Lean_auxRecExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_auxRecExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_auxRecExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_auxRecExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_auxRecExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_auxRecExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_auxRecExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_auxRecExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* lean_mark_aux_recursor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_auxRecExt;
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_4;
}
}
uint8_t lean_is_aux_recursor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_auxRecExt;
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_isAuxRecursor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_aux_recursor(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_isCasesOnRecursor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_isCasesOnRecursor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_isCasesOnRecursor_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_isCasesOnRecursor(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_casesOnSuffix;
x_5 = lean_string_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_auxRecExt;
x_8 = l_Lean_TagDeclarationExtension_isTagged(x_7, x_1, x_2);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
lean_object* l_Lean_isCasesOnRecursor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isCasesOnRecursor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
#define _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("noConf");\
__INIT_VAR__ = x_1; goto l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__1_end;\
}\
l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__1_end: ((void) 0);}
#define _init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__2_end;\
}\
l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__2_end: ((void) 0);}
lean_object* l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__2;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_noConfusionExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_noConfusionExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_noConfusionExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_noConfusionExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_instInhabitedError___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_noConfusionExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_noConfusionExt___elambda__4___rarg), 1, 0);
return x_3;
}
}
#define _init_l_Lean_noConfusionExt___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_noConfusionExt___elambda__4___boxed), 2, 0);\
__INIT_VAR__ = x_1; goto l_Lean_noConfusionExt___closed__1_end;\
}\
l_Lean_noConfusionExt___closed__1_end: ((void) 0);}
#define _init_l_Lean_noConfusionExt___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_noConfusionExt___elambda__3___boxed), 2, 0);\
__INIT_VAR__ = x_1; goto l_Lean_noConfusionExt___closed__2_end;\
}\
l_Lean_noConfusionExt___closed__2_end: ((void) 0);}
#define _init_l_Lean_noConfusionExt___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_noConfusionExt___elambda__2___boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_noConfusionExt___closed__3_end;\
}\
l_Lean_noConfusionExt___closed__3_end: ((void) 0);}
#define _init_l_Lean_noConfusionExt___closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_noConfusionExt___elambda__1___boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_noConfusionExt___closed__4_end;\
}\
l_Lean_noConfusionExt___closed__4_end: ((void) 0);}
#define _init_l_Lean_noConfusionExt___closed__5(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; \
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;\
x_2 = lean_box(0);\
x_3 = l_Lean_noConfusionExt___closed__1;\
x_4 = l_Lean_noConfusionExt___closed__2;\
x_5 = l_Lean_noConfusionExt___closed__3;\
x_6 = l_Lean_noConfusionExt___closed__4;\
x_7 = lean_alloc_ctor(0, 6, 0);\
lean_ctor_set(x_7, 0, x_1);\
lean_ctor_set(x_7, 1, x_2);\
lean_ctor_set(x_7, 2, x_3);\
lean_ctor_set(x_7, 3, x_4);\
lean_ctor_set(x_7, 4, x_5);\
lean_ctor_set(x_7, 5, x_6);\
__INIT_VAR__ = x_7; goto l_Lean_noConfusionExt___closed__5_end;\
}\
l_Lean_noConfusionExt___closed__5_end: ((void) 0);}
lean_object* l_Lean_noConfusionExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_noConfusionExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_noConfusionExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_noConfusionExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_noConfusionExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_noConfusionExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_noConfusionExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_noConfusionExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* lean_mark_no_confusion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_noConfusionExt;
x_4 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_3, x_1, x_2);
return x_4;
}
}
uint8_t lean_is_no_confusion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_noConfusionExt;
x_4 = l_Lean_TagDeclarationExtension_isTagged(x_3, x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_isNoConfusion___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_no_confusion(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_AuxRecursor(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
_init_l_Lean_casesOnSuffix___closed__1(l_Lean_casesOnSuffix___closed__1);
lean_mark_persistent(l_Lean_casesOnSuffix___closed__1);
_init_l_Lean_casesOnSuffix(l_Lean_casesOnSuffix);
lean_mark_persistent(l_Lean_casesOnSuffix);
_init_l_Lean_recOnSuffix___closed__1(l_Lean_recOnSuffix___closed__1);
lean_mark_persistent(l_Lean_recOnSuffix___closed__1);
_init_l_Lean_recOnSuffix(l_Lean_recOnSuffix);
lean_mark_persistent(l_Lean_recOnSuffix);
_init_l_Lean_brecOnSuffix___closed__1(l_Lean_brecOnSuffix___closed__1);
lean_mark_persistent(l_Lean_brecOnSuffix___closed__1);
_init_l_Lean_brecOnSuffix(l_Lean_brecOnSuffix);
lean_mark_persistent(l_Lean_brecOnSuffix);
_init_l_Lean_binductionOnSuffix___closed__1(l_Lean_binductionOnSuffix___closed__1);
lean_mark_persistent(l_Lean_binductionOnSuffix___closed__1);
_init_l_Lean_binductionOnSuffix(l_Lean_binductionOnSuffix);
lean_mark_persistent(l_Lean_binductionOnSuffix);
_init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__1(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__1);
lean_mark_persistent(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__1);
_init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__2(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__2);
lean_mark_persistent(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39____closed__2);
_init_l_Lean_auxRecExt___closed__1(l_Lean_auxRecExt___closed__1);
lean_mark_persistent(l_Lean_auxRecExt___closed__1);
_init_l_Lean_auxRecExt___closed__2(l_Lean_auxRecExt___closed__2);
lean_mark_persistent(l_Lean_auxRecExt___closed__2);
_init_l_Lean_auxRecExt___closed__3(l_Lean_auxRecExt___closed__3);
lean_mark_persistent(l_Lean_auxRecExt___closed__3);
_init_l_Lean_auxRecExt___closed__4(l_Lean_auxRecExt___closed__4);
lean_mark_persistent(l_Lean_auxRecExt___closed__4);
_init_l_Lean_auxRecExt___closed__5(l_Lean_auxRecExt___closed__5);
lean_mark_persistent(l_Lean_auxRecExt___closed__5);
res = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_39_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_auxRecExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_auxRecExt);
lean_dec_ref(res);
_init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__1(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__1);
lean_mark_persistent(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__1);
_init_l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__2(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__2);
lean_mark_persistent(l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101____closed__2);
_init_l_Lean_noConfusionExt___closed__1(l_Lean_noConfusionExt___closed__1);
lean_mark_persistent(l_Lean_noConfusionExt___closed__1);
_init_l_Lean_noConfusionExt___closed__2(l_Lean_noConfusionExt___closed__2);
lean_mark_persistent(l_Lean_noConfusionExt___closed__2);
_init_l_Lean_noConfusionExt___closed__3(l_Lean_noConfusionExt___closed__3);
lean_mark_persistent(l_Lean_noConfusionExt___closed__3);
_init_l_Lean_noConfusionExt___closed__4(l_Lean_noConfusionExt___closed__4);
lean_mark_persistent(l_Lean_noConfusionExt___closed__4);
_init_l_Lean_noConfusionExt___closed__5(l_Lean_noConfusionExt___closed__5);
lean_mark_persistent(l_Lean_noConfusionExt___closed__5);
res = l_Lean_initFn____x40_Lean_AuxRecursor___hyg_101_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_noConfusionExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_noConfusionExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
