// Lean compiler output
// Module: Lake.Util.Task
// Imports: public import Init.Control.Option public import Init.Control.Except
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
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadTask__lake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadTask__lake___closed__0 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__0_value;
static const lean_closure_object l_Lake_instMonadTask__lake___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadTask__lake___closed__0_value)} };
static const lean_object* l_Lake_instMonadTask__lake___closed__1 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__1_value;
static const lean_closure_object l_Lake_instMonadTask__lake___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadTask__lake___closed__2 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__2_value;
static const lean_closure_object l_Lake_instMonadTask__lake___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__4, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadTask__lake___closed__0_value)} };
static const lean_object* l_Lake_instMonadTask__lake___closed__3 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__3_value;
static const lean_closure_object l_Lake_instMonadTask__lake___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__5, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadTask__lake___closed__4 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__4_value;
static const lean_closure_object l_Lake_instMonadTask__lake___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__8, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadTask__lake___closed__4_value)} };
static const lean_object* l_Lake_instMonadTask__lake___closed__5 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__5_value;
static const lean_closure_object l_Lake_instMonadTask__lake___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadTask__lake___lam__10, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadTask__lake___closed__6 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__6_value;
static const lean_ctor_object l_Lake_instMonadTask__lake___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadTask__lake___closed__0_value),((lean_object*)&l_Lake_instMonadTask__lake___closed__1_value)}};
static const lean_object* l_Lake_instMonadTask__lake___closed__7 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__7_value;
static const lean_ctor_object l_Lake_instMonadTask__lake___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadTask__lake___closed__7_value),((lean_object*)&l_Lake_instMonadTask__lake___closed__2_value),((lean_object*)&l_Lake_instMonadTask__lake___closed__3_value),((lean_object*)&l_Lake_instMonadTask__lake___closed__5_value),((lean_object*)&l_Lake_instMonadTask__lake___closed__6_value)}};
static const lean_object* l_Lake_instMonadTask__lake___closed__8 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__8_value;
static const lean_ctor_object l_Lake_instMonadTask__lake___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadTask__lake___closed__8_value),((lean_object*)&l_Lake_instMonadTask__lake___closed__4_value)}};
static const lean_object* l_Lake_instMonadTask__lake___closed__9 = (const lean_object*)&l_Lake_instMonadTask__lake___closed__9_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadTask__lake = (const lean_object*)&l_Lake_instMonadTask__lake___closed__9_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadBaseIOTask = (const lean_object*)&l_Lake_instMonadTask__lake___closed__9_value;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedBaseIOTask___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedBaseIOTask(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instInhabitedOptionIOTask___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedOptionIOTask___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedOptionIOTask(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = lean_task_map(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_task_pure(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lam__3), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = lean_task_bind(x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = lean_task_bind(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_task_pure(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instMonadTask__lake___lam__6(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lam__6___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_1);
x_6 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lam__7), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instMonadTask__lake___lam__9(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadTask__lake___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lake_instMonadTask__lake___lam__9___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = lean_task_bind(x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedBaseIOTask___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lake_instMonadTask__lake));
x_3 = l_instInhabitedOfMonad___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedBaseIOTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instInhabitedBaseIOTask___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedOptionIOTask___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedOptionIOTask(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lake_instInhabitedOptionIOTask___closed__0, &l_Lake_instInhabitedOptionIOTask___closed__0_once, _init_l_Lake_instInhabitedOptionIOTask___closed__0);
return x_2;
}
}
lean_object* initialize_Init_Control_Option(uint8_t builtin);
lean_object* initialize_Init_Control_Except(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Task(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
