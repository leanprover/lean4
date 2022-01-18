// Lean compiler output
// Module: Lean.ProjFns
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
LEAN_EXPORT lean_object* lean_add_projection_info(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_projectionFnInfoExt___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_projectionFnInfoExt___elambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__2___boxed(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
static uint32_t l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_ProjFns___hyg_75____closed__2;
LEAN_EXPORT uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_projection_info(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__4___rarg(lean_object*);
static lean_object* l_Lean_projectionFnInfoExt___closed__7;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ProjFns___hyg_75_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedProjectionFunctionInfo;
lean_object* l_Lean_mkMapDeclarationExtension___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addProjectionFnInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedProjectionFunctionInfo___closed__1;
static lean_object* l_Lean_projectionFnInfoExt___closed__5;
LEAN_EXPORT uint8_t lean_projection_info_from_class(lean_object*);
static lean_object* l_Lean_projectionFnInfoExt___closed__3;
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt;
static lean_object* l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__2;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ProjectionFunctionInfo_fromClassEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkProjectionInfoEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_projectionFnInfoExt___closed__1;
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f(lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_projectionFnInfoExt___closed__4;
LEAN_EXPORT lean_object* l_Lean_Environment_isProjectionFn___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_projectionFnInfoExt___closed__2;
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_projection_info(lean_object*, lean_object*, lean_object*, uint8_t);
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_ProjFns___hyg_75____closed__1;
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__1___boxed(lean_object*);
static lean_object* _init_l_Lean_instInhabitedProjectionFunctionInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = 0;
x_4 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedProjectionFunctionInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedProjectionFunctionInfo___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* lean_mk_projection_info(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProjectionInfoEx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = lean_mk_projection_info(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lean_projection_info_from_class(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ProjectionFunctionInfo_fromClassEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_projection_info_from_class(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ProjFns___hyg_75____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("projinfo");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ProjFns___hyg_75____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_ProjFns___hyg_75____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ProjFns___hyg_75_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_instInhabitedProjectionFunctionInfo;
x_3 = l_Lean_initFn____x40_Lean_ProjFns___hyg_75____closed__2;
x_4 = l_Lean_mkMapDeclarationExtension___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_projectionFnInfoExt___elambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_projectionFnInfoExt___elambda__2___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static uint32_t _init_l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__3() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__1;
x_3 = l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__2;
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_projectionFnInfoExt___elambda__4___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_projectionFnInfoExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_projectionFnInfoExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_projectionFnInfoExt___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_projectionFnInfoExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_projectionFnInfoExt___elambda__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_projectionFnInfoExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_projectionFnInfoExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_projectionFnInfoExt___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_projectionFnInfoExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_projectionFnInfoExt___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_projectionFnInfoExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_projectionFnInfoExt___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_projectionFnInfoExt___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_projectionFnInfoExt___closed__3;
x_4 = l_Lean_projectionFnInfoExt___closed__4;
x_5 = l_Lean_projectionFnInfoExt___closed__5;
x_6 = l_Lean_projectionFnInfoExt___closed__6;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_projectionFnInfoExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_projectionFnInfoExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_projectionFnInfoExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_projectionFnInfoExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_add_projection_info(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*3, x_6);
x_8 = l_Lean_projectionFnInfoExt;
x_9 = l_Lean_MapDeclarationExtension_insert___rarg(x_8, x_1, x_2, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addProjectionFnInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = lean_add_projection_info(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lean_get_projection_info(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedProjectionFunctionInfo;
x_4 = l_Lean_projectionFnInfoExt;
x_5 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_isProjectionFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_instInhabitedProjectionFunctionInfo;
x_4 = l_Lean_projectionFnInfoExt;
x_5 = l_Lean_MapDeclarationExtension_contains___rarg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_isProjectionFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_isProjectionFn(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedProjectionFunctionInfo;
x_4 = l_Lean_projectionFnInfoExt;
lean_inc(x_1);
x_5 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_3, x_4, x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_environment_find(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
if (lean_obj_tag(x_12) == 6)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; 
lean_free_object(x_9);
lean_dec(x_12);
x_15 = lean_box(0);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
if (lean_obj_tag(x_16) == 6)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_16);
x_20 = lean_box(0);
return x_20;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_instInhabitedProjectionFunctionInfo;
x_7 = l_Lean_projectionFnInfoExt;
x_8 = l_Lean_MapDeclarationExtension_contains___rarg(x_6, x_7, x_3, x_2);
x_9 = lean_box(x_8);
x_10 = lean_apply_2(x_5, lean_box(0), x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_isProjectionFn___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_isProjectionFn___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_instInhabitedProjectionFunctionInfo;
x_7 = l_Lean_projectionFnInfoExt;
x_8 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_6, x_7, x_3, x_2);
x_9 = lean_apply_2(x_5, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_getProjectionFnInfo_x3f___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getProjectionFnInfo_x3f___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ProjFns(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedProjectionFunctionInfo___closed__1 = _init_l_Lean_instInhabitedProjectionFunctionInfo___closed__1();
lean_mark_persistent(l_Lean_instInhabitedProjectionFunctionInfo___closed__1);
l_Lean_instInhabitedProjectionFunctionInfo = _init_l_Lean_instInhabitedProjectionFunctionInfo();
lean_mark_persistent(l_Lean_instInhabitedProjectionFunctionInfo);
l_Lean_initFn____x40_Lean_ProjFns___hyg_75____closed__1 = _init_l_Lean_initFn____x40_Lean_ProjFns___hyg_75____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ProjFns___hyg_75____closed__1);
l_Lean_initFn____x40_Lean_ProjFns___hyg_75____closed__2 = _init_l_Lean_initFn____x40_Lean_ProjFns___hyg_75____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ProjFns___hyg_75____closed__2);
l_Lean_projectionFnInfoExt___elambda__2___closed__1 = _init_l_Lean_projectionFnInfoExt___elambda__2___closed__1();
lean_mark_persistent(l_Lean_projectionFnInfoExt___elambda__2___closed__1);
l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__1 = _init_l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__1();
l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__2 = _init_l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__2();
lean_mark_persistent(l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__2);
l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__3 = _init_l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__3();
lean_mark_persistent(l_Lean_projectionFnInfoExt___elambda__4___rarg___closed__3);
l_Lean_projectionFnInfoExt___closed__1 = _init_l_Lean_projectionFnInfoExt___closed__1();
lean_mark_persistent(l_Lean_projectionFnInfoExt___closed__1);
l_Lean_projectionFnInfoExt___closed__2 = _init_l_Lean_projectionFnInfoExt___closed__2();
lean_mark_persistent(l_Lean_projectionFnInfoExt___closed__2);
l_Lean_projectionFnInfoExt___closed__3 = _init_l_Lean_projectionFnInfoExt___closed__3();
lean_mark_persistent(l_Lean_projectionFnInfoExt___closed__3);
l_Lean_projectionFnInfoExt___closed__4 = _init_l_Lean_projectionFnInfoExt___closed__4();
lean_mark_persistent(l_Lean_projectionFnInfoExt___closed__4);
l_Lean_projectionFnInfoExt___closed__5 = _init_l_Lean_projectionFnInfoExt___closed__5();
lean_mark_persistent(l_Lean_projectionFnInfoExt___closed__5);
l_Lean_projectionFnInfoExt___closed__6 = _init_l_Lean_projectionFnInfoExt___closed__6();
lean_mark_persistent(l_Lean_projectionFnInfoExt___closed__6);
l_Lean_projectionFnInfoExt___closed__7 = _init_l_Lean_projectionFnInfoExt___closed__7();
lean_mark_persistent(l_Lean_projectionFnInfoExt___closed__7);
res = l_Lean_initFn____x40_Lean_ProjFns___hyg_75_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_projectionFnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_projectionFnInfoExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
