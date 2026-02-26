// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Fin
// Imports: public import Init.Data.Range.Polymorphic.Instances public import Init.Data.Fin.OverflowAware import Init.Grind import Init.Data.Fin.Lemmas import Init.Data.Int.OfNat import Init.Data.Nat.Linear import Init.Data.Option.Lemmas
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNatNat;
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Fin_instHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Fin_instHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_instHasSize___closed__0 = (const lean_object*)&l_Fin_instHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_Fin_instHasSize(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Fin_instHasSize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Fin_instHasSize__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_instHasSize__1___closed__0 = (const lean_object*)&l_Fin_instHasSize__1___closed__0_value;
LEAN_EXPORT lean_object* l_Fin_instHasSize__1(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__2(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_nat_dec_lt(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_instUpwardEnumerable___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_nat_add(x_3, x_2);
x_5 = lean_nat_dec_lt(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_instUpwardEnumerable___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Fin_instUpwardEnumerable___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Fin_instUpwardEnumerable___lam__1___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Fin_instLeast_x3fOfNatNat(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_instLeast_x3fOfNeZeroNat___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_instLeast_x3fOfNeZeroNat___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_instLeast_x3fOfNeZeroNat(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_nat_sub(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_instHasSize___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Fin_instHasSize___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_instHasSize(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_nat_sub(x_4, x_1);
lean_dec(x_4);
x_6 = lean_nat_sub(x_5, x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_instHasSize__1___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Fin_instHasSize__1___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_instHasSize__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__2___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_instHasSize__2___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_instHasSize__2___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_OverflowAware(uint8_t builtin);
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Fin(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_OverflowAware(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Fin_instLeast_x3fOfNatNat = _init_l_Fin_instLeast_x3fOfNatNat();
lean_mark_persistent(l_Fin_instLeast_x3fOfNatNat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
