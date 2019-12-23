// Lean compiler output
// Module: Init.Lean.Declaration
// Imports: Init.Lean.Expr
#include "runtime/lean.h"
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
lean_object* l_Lean_ReducibilityHints_lt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ConstantVal_inhabited___closed__1;
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_instantiateValueLevelParams___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ConstantVal_inhabited___closed__2;
lean_object* l_Lean_ConstantInfo_value_x3f___boxed(lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x21___closed__1;
lean_object* l_Lean_ConstantInfo_lparams___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x21___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x21___closed__2;
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l_Lean_ConstantInfo_instantiateTypeLevelParams___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t l_UInt32_decLt(uint32_t, uint32_t);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object*);
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_ConstantVal_inhabited;
lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
lean_object* l_Lean_RecursorVal_getInduct___boxed(lean_object*);
lean_object* l_Lean_ReducibilityHints_Inhabited;
lean_object* l_Lean_ConstantInfo_isCtor___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_hints(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*);
lean_object* l_Lean_ConstructorVal_inhabited___closed__1;
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isCtor(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_nctors___boxed(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_ConstantInfo_name___boxed(lean_object*);
lean_object* l_Lean_ConstructorVal_inhabited;
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_InductiveVal_nctors(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x21___closed__3;
lean_object* l_Lean_ConstantInfo_value_x21(lean_object*);
lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object*);
lean_object* lean_task_get(lean_object*);
lean_object* l_Lean_ConstantInfo_type___boxed(lean_object*);
uint8_t l_Lean_ReducibilityHints_lt(lean_object*, lean_object*);
lean_object* _init_l_Lean_ReducibilityHints_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint8_t l_Lean_ReducibilityHints_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
case 1:
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
default: 
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_ctor_get_uint32(x_1, 0);
x_9 = lean_ctor_get_uint32(x_2, 0);
x_10 = x_8 < x_9;
return x_10;
}
}
}
}
}
}
lean_object* l_Lean_ReducibilityHints_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_ReducibilityHints_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_ConstantVal_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_ConstantVal_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_ConstantVal_inhabited___closed__1;
x_3 = l_Lean_Expr_Inhabited___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_ConstantVal_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ConstantVal_inhabited___closed__2;
return x_1;
}
}
lean_object* l_Lean_InductiveVal_nctors(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthAux___main___rarg(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_InductiveVal_nctors___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_InductiveVal_nctors(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ConstructorVal_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_ConstantVal_inhabited___closed__2;
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = 1;
x_5 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*5, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_ConstructorVal_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ConstructorVal_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_1, 4);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_ctor_get(x_1, 5);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Lean_RecursorVal_getMajorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RecursorVal_getMajorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_RecursorVal_getInduct(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_Name_getPrefix(x_3);
return x_4;
}
}
lean_object* l_Lean_RecursorVal_getInduct___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RecursorVal_getInduct(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantInfo_toConstantVal(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_ConstantInfo_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_ConstantInfo_toConstantVal(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_ConstantInfo_name___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantInfo_name(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_ConstantInfo_lparams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_ConstantInfo_toConstantVal(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_ConstantInfo_lparams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantInfo_lparams(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_ConstantInfo_type(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_ConstantInfo_toConstantVal(x_1);
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_ConstantInfo_type___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantInfo_type(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_task_get(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
}
}
lean_object* l_Lean_ConstantInfo_value_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantInfo_value_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_ConstantInfo_hasValue(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 2:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
default: 
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
}
lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_ConstantInfo_hasValue(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.Declaration");
return x_1;
}
}
lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declaration with value expected");
return x_1;
}
}
lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_ConstantInfo_value_x21___closed__1;
x_2 = lean_unsigned_to_nat(199u);
x_3 = lean_unsigned_to_nat(31u);
x_4 = l_Lean_ConstantInfo_value_x21___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_ConstantInfo_value_x21(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_task_get(x_5);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Expr_Inhabited;
x_8 = l_Lean_ConstantInfo_value_x21___closed__3;
x_9 = lean_panic_fn(x_7, x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_ConstantInfo_value_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantInfo_value_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_ConstantInfo_hints(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
}
lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantInfo_hints(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_ConstantInfo_isCtor(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_ConstantInfo_isCtor___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_ConstantInfo_isCtor(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_ConstantInfo_instantiateTypeLevelParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_instantiate_type_lparams(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_ConstantInfo_instantiateValueLevelParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_instantiate_value_lparams(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Declaration(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_ReducibilityHints_Inhabited = _init_l_Lean_ReducibilityHints_Inhabited();
lean_mark_persistent(l_Lean_ReducibilityHints_Inhabited);
l_Lean_ConstantVal_inhabited___closed__1 = _init_l_Lean_ConstantVal_inhabited___closed__1();
lean_mark_persistent(l_Lean_ConstantVal_inhabited___closed__1);
l_Lean_ConstantVal_inhabited___closed__2 = _init_l_Lean_ConstantVal_inhabited___closed__2();
lean_mark_persistent(l_Lean_ConstantVal_inhabited___closed__2);
l_Lean_ConstantVal_inhabited = _init_l_Lean_ConstantVal_inhabited();
lean_mark_persistent(l_Lean_ConstantVal_inhabited);
l_Lean_ConstructorVal_inhabited___closed__1 = _init_l_Lean_ConstructorVal_inhabited___closed__1();
lean_mark_persistent(l_Lean_ConstructorVal_inhabited___closed__1);
l_Lean_ConstructorVal_inhabited = _init_l_Lean_ConstructorVal_inhabited();
lean_mark_persistent(l_Lean_ConstructorVal_inhabited);
l_Lean_ConstantInfo_value_x21___closed__1 = _init_l_Lean_ConstantInfo_value_x21___closed__1();
lean_mark_persistent(l_Lean_ConstantInfo_value_x21___closed__1);
l_Lean_ConstantInfo_value_x21___closed__2 = _init_l_Lean_ConstantInfo_value_x21___closed__2();
lean_mark_persistent(l_Lean_ConstantInfo_value_x21___closed__2);
l_Lean_ConstantInfo_value_x21___closed__3 = _init_l_Lean_ConstantInfo_value_x21___closed__3();
lean_mark_persistent(l_Lean_ConstantInfo_value_x21___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
