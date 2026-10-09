// Lean compiler output
// Module: Init.Data.Option.Basic
// Imports: public import Init.Control.Basic public import Init.Grind.Tactics
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Option_map(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_decidableEqNone___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_decidableEqNone___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Option_decidableEqNone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_decidableEqNone___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_decidableNoneEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_decidableNoneEq___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Option_decidableNoneEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_decidableNoneEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_isSome___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_isSome___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Option_isSome(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_isSome___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_isNone___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_isNone___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Option_isNone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_isNone___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_isEqSome___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_isEqSome___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_isEqSome(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_isEqSome___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_bind___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_bind(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_bindM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_bindM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_mapM___redArg___lam__0(lean_object*);
static const lean_closure_object l_Option_mapM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_mapM___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Option_mapM___redArg___closed__0 = (const lean_object*)&l_Option_mapM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Option_mapM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_mapA___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_mapA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_filterM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Option_filterM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_filterM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_filterM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_filter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_all(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_all___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_any(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_any___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Option_instOrElse___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_instOrElse___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Option_instOrElse___redArg___closed__0 = (const lean_object*)&l_Option_instOrElse___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg();
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_instOrElse(lean_object*);
LEAN_EXPORT uint8_t l_Option_instDecidableRelLt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instDecidableRelLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instDecidableRelLe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableRelLe___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instDecidableRelLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableRelLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_merge___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_merge(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_elim___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_elim___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_get___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_get___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_guard___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_guard(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_toList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_toList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toList___boxed(lean_object*, lean_object*);
static const lean_array_object l_Option_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Option_toArray___redArg___closed__0 = (const lean_object*)&l_Option_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Option_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_join___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_join___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_join___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_sequence___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_sequence(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_elimM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_elimM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_elimM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_elimM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getDM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getDM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getDM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getDM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_min___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_min(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instMin___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_instMin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_max___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_max(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instMax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_instMax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instLTOption___redArg();
LEAN_EXPORT lean_object* l_instLTOption___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instLTOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instLEOption___redArg();
LEAN_EXPORT lean_object* l_instLEOption___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instLEOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instFunctorOption___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instFunctorOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instFunctorOption___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instFunctorOption___closed__0 = (const lean_object*)&l_instFunctorOption___closed__0_value;
static const lean_closure_object l_instFunctorOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_map, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instFunctorOption___closed__1 = (const lean_object*)&l_instFunctorOption___closed__1_value;
static const lean_ctor_object l_instFunctorOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instFunctorOption___closed__1_value),((lean_object*)&l_instFunctorOption___closed__0_value)}};
static const lean_object* l_instFunctorOption___closed__2 = (const lean_object*)&l_instFunctorOption___closed__2_value;
LEAN_EXPORT const lean_object* l_instFunctorOption = (const lean_object*)&l_instFunctorOption___closed__2_value;
LEAN_EXPORT lean_object* l_instMonadOption___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadOption___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadOption___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadOption___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadOption___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadOption___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadOption___closed__0 = (const lean_object*)&l_instMonadOption___closed__0_value;
static const lean_closure_object l_instMonadOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadOption___closed__1 = (const lean_object*)&l_instMonadOption___closed__1_value;
static const lean_closure_object l_instMonadOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadOption___closed__2 = (const lean_object*)&l_instMonadOption___closed__2_value;
static const lean_closure_object l_instMonadOption___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadOption___closed__3 = (const lean_object*)&l_instMonadOption___closed__3_value;
static const lean_ctor_object l_instMonadOption___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_instFunctorOption___closed__2_value),((lean_object*)&l_instMonadOption___closed__0_value),((lean_object*)&l_instMonadOption___closed__1_value),((lean_object*)&l_instMonadOption___closed__2_value),((lean_object*)&l_instMonadOption___closed__3_value)}};
static const lean_object* l_instMonadOption___closed__4 = (const lean_object*)&l_instMonadOption___closed__4_value;
static const lean_closure_object l_instMonadOption___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_bind, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadOption___closed__5 = (const lean_object*)&l_instMonadOption___closed__5_value;
static const lean_ctor_object l_instMonadOption___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadOption___closed__4_value),((lean_object*)&l_instMonadOption___closed__5_value)}};
static const lean_object* l_instMonadOption___closed__6 = (const lean_object*)&l_instMonadOption___closed__6_value;
LEAN_EXPORT const lean_object* l_instMonadOption = (const lean_object*)&l_instMonadOption___closed__6_value;
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instAlternativeOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instAlternativeOption___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAlternativeOption___closed__0 = (const lean_object*)&l_instAlternativeOption___closed__0_value;
static const lean_closure_object l_instAlternativeOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instAlternativeOption___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAlternativeOption___closed__1 = (const lean_object*)&l_instAlternativeOption___closed__1_value;
static const lean_ctor_object l_instAlternativeOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadOption___closed__4_value),((lean_object*)&l_instAlternativeOption___closed__0_value),((lean_object*)&l_instAlternativeOption___closed__1_value)}};
static const lean_object* l_instAlternativeOption___closed__2 = (const lean_object*)&l_instAlternativeOption___closed__2_value;
LEAN_EXPORT const lean_object* l_instAlternativeOption = (const lean_object*)&l_instAlternativeOption___closed__2_value;
LEAN_EXPORT lean_object* l_liftOption___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftOption(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_tryCatch___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_tryCatch___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_tryCatch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_tryCatch___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instMonadExceptOfUnitOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadExceptOfUnitOption___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadExceptOfUnitOption___closed__0 = (const lean_object*)&l_instMonadExceptOfUnitOption___closed__0_value;
static const lean_closure_object l_instMonadExceptOfUnitOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_tryCatch___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadExceptOfUnitOption___closed__1 = (const lean_object*)&l_instMonadExceptOfUnitOption___closed__1_value;
static const lean_ctor_object l_instMonadExceptOfUnitOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadExceptOfUnitOption___closed__0_value),((lean_object*)&l_instMonadExceptOfUnitOption___closed__1_value)}};
static const lean_object* l_instMonadExceptOfUnitOption___closed__2 = (const lean_object*)&l_instMonadExceptOfUnitOption___closed__2_value;
LEAN_EXPORT const lean_object* l_instMonadExceptOfUnitOption = (const lean_object*)&l_instMonadExceptOfUnitOption___closed__2_value;
uint8_t l_Option_instDecidableEq___redArg(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
if (lean_obj_tag(v_a_2_) == 0)
{
lean_dec_ref(v_inst_1_);
if (lean_obj_tag(v_b_3_) == 0)
{
uint8_t v___x_4_; 
v___x_4_ = 1;
return v___x_4_;
}
else
{
uint8_t v___x_5_; 
lean_dec_ref_known(v_b_3_, 1);
v___x_5_ = 0;
return v___x_5_;
}
}
else
{
if (lean_obj_tag(v_b_3_) == 0)
{
uint8_t v___x_6_; 
lean_dec_ref_known(v_a_2_, 1);
lean_dec_ref(v_inst_1_);
v___x_6_ = 0;
return v___x_6_;
}
else
{
lean_object* v_val_7_; lean_object* v_val_8_; lean_object* v_decide_9_; uint8_t v___x_10_; 
v_val_7_ = lean_ctor_get(v_a_2_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v_a_2_, 1);
v_val_8_ = lean_ctor_get(v_b_3_, 0);
lean_inc(v_val_8_);
lean_dec_ref_known(v_b_3_, 1);
v_decide_9_ = lean_apply_2(v_inst_1_, v_val_7_, v_val_8_);
v___x_10_ = lean_unbox(v_decide_9_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT void l_Option_instDecidableEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_b_3_ = stack[2].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Option_instDecidableEq___redArg(v_inst_1_, v_a_2_, v_b_3_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Option_instDecidableEq___redArg___boxed(lean_object* v_inst_12_, lean_object* v_a_13_, lean_object* v_b_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Option_instDecidableEq___redArg(v_inst_12_, v_a_13_, v_b_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
uint8_t l_Option_instDecidableEq(lean_object* v_00_u03b1_17_, lean_object* v_inst_18_, lean_object* v_a_19_, lean_object* v_b_20_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = l_Option_instDecidableEq___redArg(v_inst_18_, v_a_19_, v_b_20_);
return v___x_21_;
}
}
LEAN_EXPORT void l_Option_instDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_18_ = stack[1].m_obj;
lean_object* v_a_19_ = stack[2].m_obj;
lean_object* v_b_20_ = stack[3].m_obj;
uint8_t v_res_22_;
v_res_22_ = l_Option_instDecidableEq(lean_box(0), v_inst_18_, v_a_19_, v_b_20_);
stack->m_num = v_res_22_;
}
LEAN_EXPORT lean_object* l_Option_instDecidableEq___boxed(lean_object* v_00_u03b1_23_, lean_object* v_inst_24_, lean_object* v_a_25_, lean_object* v_b_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Option_instDecidableEq(v_00_u03b1_23_, v_inst_24_, v_a_25_, v_b_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
uint8_t l_Option_decidableEqNone___redArg(lean_object* v_o_29_){
_start:
{
if (lean_obj_tag(v_o_29_) == 0)
{
uint8_t v___x_30_; 
v___x_30_ = 1;
return v___x_30_;
}
else
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
}
}
LEAN_EXPORT void l_Option_decidableEqNone___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_29_ = stack[0].m_obj;
uint8_t v_res_32_;
v_res_32_ = l_Option_decidableEqNone___redArg(v_o_29_);
stack->m_num = v_res_32_;
}
LEAN_EXPORT lean_object* l_Option_decidableEqNone___redArg___boxed(lean_object* v_o_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Option_decidableEqNone___redArg(v_o_33_);
lean_dec(v_o_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
uint8_t l_Option_decidableEqNone(lean_object* v_00_u03b1_36_, lean_object* v_o_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = l_Option_decidableEqNone___redArg(v_o_37_);
return v___x_38_;
}
}
LEAN_EXPORT void l_Option_decidableEqNone_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_37_ = stack[1].m_obj;
uint8_t v_res_39_;
v_res_39_ = l_Option_decidableEqNone(lean_box(0), v_o_37_);
stack->m_num = v_res_39_;
}
LEAN_EXPORT lean_object* l_Option_decidableEqNone___boxed(lean_object* v_00_u03b1_40_, lean_object* v_o_41_){
_start:
{
uint8_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = l_Option_decidableEqNone(v_00_u03b1_40_, v_o_41_);
lean_dec(v_o_41_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
uint8_t l_Option_decidableNoneEq___redArg(lean_object* v_o_44_){
_start:
{
if (lean_obj_tag(v_o_44_) == 0)
{
uint8_t v___x_45_; 
v___x_45_ = 1;
return v___x_45_;
}
else
{
uint8_t v___x_46_; 
v___x_46_ = 0;
return v___x_46_;
}
}
}
LEAN_EXPORT void l_Option_decidableNoneEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_44_ = stack[0].m_obj;
uint8_t v_res_47_;
v_res_47_ = l_Option_decidableNoneEq___redArg(v_o_44_);
stack->m_num = v_res_47_;
}
LEAN_EXPORT lean_object* l_Option_decidableNoneEq___redArg___boxed(lean_object* v_o_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Option_decidableNoneEq___redArg(v_o_48_);
lean_dec(v_o_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
uint8_t l_Option_decidableNoneEq(lean_object* v_00_u03b1_51_, lean_object* v_o_52_){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = l_Option_decidableNoneEq___redArg(v_o_52_);
return v___x_53_;
}
}
LEAN_EXPORT void l_Option_decidableNoneEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_52_ = stack[1].m_obj;
uint8_t v_res_54_;
v_res_54_ = l_Option_decidableNoneEq(lean_box(0), v_o_52_);
stack->m_num = v_res_54_;
}
LEAN_EXPORT lean_object* l_Option_decidableNoneEq___boxed(lean_object* v_00_u03b1_55_, lean_object* v_o_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l_Option_decidableNoneEq(v_00_u03b1_55_, v_o_56_);
lean_dec(v_o_56_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT lean_object* l_Option_getM___redArg(lean_object* v_inst_59_, lean_object* v_x_60_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v_failure_61_; lean_object* v___x_62_; 
v_failure_61_ = lean_ctor_get(v_inst_59_, 1);
lean_inc(v_failure_61_);
lean_dec_ref(v_inst_59_);
v___x_62_ = lean_apply_1(v_failure_61_, lean_box(0));
return v___x_62_;
}
else
{
lean_object* v_toApplicative_63_; lean_object* v_toPure_64_; lean_object* v_val_65_; lean_object* v___x_66_; 
v_toApplicative_63_ = lean_ctor_get(v_inst_59_, 0);
lean_inc_ref(v_toApplicative_63_);
lean_dec_ref(v_inst_59_);
v_toPure_64_ = lean_ctor_get(v_toApplicative_63_, 1);
lean_inc(v_toPure_64_);
lean_dec_ref(v_toApplicative_63_);
v_val_65_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_val_65_);
lean_dec_ref_known(v_x_60_, 1);
v___x_66_ = lean_apply_2(v_toPure_64_, lean_box(0), v_val_65_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Option_getM(lean_object* v_m_67_, lean_object* v_00_u03b1_68_, lean_object* v_inst_69_, lean_object* v_x_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Option_getM___redArg(v_inst_69_, v_x_70_);
return v___x_71_;
}
}
uint8_t l_Option_isSome___redArg(lean_object* v_x_72_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
else
{
uint8_t v___x_74_; 
v___x_74_ = 1;
return v___x_74_;
}
}
}
LEAN_EXPORT void l_Option_isSome___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_72_ = stack[0].m_obj;
uint8_t v_res_75_;
v_res_75_ = l_Option_isSome___redArg(v_x_72_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l_Option_isSome___redArg___boxed(lean_object* v_x_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Option_isSome___redArg(v_x_76_);
lean_dec(v_x_76_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
uint8_t l_Option_isSome(lean_object* v_00_u03b1_79_, lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 1;
return v___x_82_;
}
}
}
LEAN_EXPORT void l_Option_isSome_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_80_ = stack[1].m_obj;
uint8_t v_res_83_;
v_res_83_ = l_Option_isSome(lean_box(0), v_x_80_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l_Option_isSome___boxed(lean_object* v_00_u03b1_84_, lean_object* v_x_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Option_isSome(v_00_u03b1_84_, v_x_85_);
lean_dec(v_x_85_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
uint8_t l_Option_isNone___redArg(lean_object* v_x_88_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
uint8_t v___x_89_; 
v___x_89_ = 1;
return v___x_89_;
}
else
{
uint8_t v___x_90_; 
v___x_90_ = 0;
return v___x_90_;
}
}
}
LEAN_EXPORT void l_Option_isNone___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_88_ = stack[0].m_obj;
uint8_t v_res_91_;
v_res_91_ = l_Option_isNone___redArg(v_x_88_);
stack->m_num = v_res_91_;
}
LEAN_EXPORT lean_object* l_Option_isNone___redArg___boxed(lean_object* v_x_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Option_isNone___redArg(v_x_92_);
lean_dec(v_x_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
uint8_t l_Option_isNone(lean_object* v_00_u03b1_95_, lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
uint8_t v___x_97_; 
v___x_97_ = 1;
return v___x_97_;
}
else
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
}
LEAN_EXPORT void l_Option_isNone_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_96_ = stack[1].m_obj;
uint8_t v_res_99_;
v_res_99_ = l_Option_isNone(lean_box(0), v_x_96_);
stack->m_num = v_res_99_;
}
LEAN_EXPORT lean_object* l_Option_isNone___boxed(lean_object* v_00_u03b1_100_, lean_object* v_x_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Option_isNone(v_00_u03b1_100_, v_x_101_);
lean_dec(v_x_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
uint8_t l_Option_isEqSome___redArg(lean_object* v_inst_104_, lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
uint8_t v___x_107_; 
lean_dec(v_x_106_);
lean_dec_ref(v_inst_104_);
v___x_107_ = 0;
return v___x_107_;
}
else
{
lean_object* v_val_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v_val_108_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_val_108_);
lean_dec_ref_known(v_x_105_, 1);
v___x_109_ = lean_apply_2(v_inst_104_, v_val_108_, v_x_106_);
v___x_110_ = lean_unbox(v___x_109_);
return v___x_110_;
}
}
}
LEAN_EXPORT void l_Option_isEqSome___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_104_ = stack[0].m_obj;
lean_object* v_x_105_ = stack[1].m_obj;
lean_object* v_x_106_ = stack[2].m_obj;
uint8_t v_res_111_;
v_res_111_ = l_Option_isEqSome___redArg(v_inst_104_, v_x_105_, v_x_106_);
stack->m_num = v_res_111_;
}
LEAN_EXPORT lean_object* l_Option_isEqSome___redArg___boxed(lean_object* v_inst_112_, lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Option_isEqSome___redArg(v_inst_112_, v_x_113_, v_x_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
uint8_t l_Option_isEqSome(lean_object* v_00_u03b1_117_, lean_object* v_inst_118_, lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
if (lean_obj_tag(v_x_119_) == 0)
{
uint8_t v___x_121_; 
lean_dec(v_x_120_);
lean_dec_ref(v_inst_118_);
v___x_121_ = 0;
return v___x_121_;
}
else
{
lean_object* v_val_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_val_122_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_val_122_);
lean_dec_ref_known(v_x_119_, 1);
v___x_123_ = lean_apply_2(v_inst_118_, v_val_122_, v_x_120_);
v___x_124_ = lean_unbox(v___x_123_);
return v___x_124_;
}
}
}
LEAN_EXPORT void l_Option_isEqSome_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_118_ = stack[1].m_obj;
lean_object* v_x_119_ = stack[2].m_obj;
lean_object* v_x_120_ = stack[3].m_obj;
uint8_t v_res_125_;
v_res_125_ = l_Option_isEqSome(lean_box(0), v_inst_118_, v_x_119_, v_x_120_);
stack->m_num = v_res_125_;
}
LEAN_EXPORT lean_object* l_Option_isEqSome___boxed(lean_object* v_00_u03b1_126_, lean_object* v_inst_127_, lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Option_isEqSome(v_00_u03b1_126_, v_inst_127_, v_x_128_, v_x_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* l_Option_bind___redArg(lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_object* v___x_134_; 
lean_dec_ref(v_x_133_);
v___x_134_ = lean_box(0);
return v___x_134_;
}
else
{
lean_object* v_val_135_; lean_object* v___x_136_; 
v_val_135_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_val_135_);
lean_dec_ref_known(v_x_132_, 1);
v___x_136_ = lean_apply_1(v_x_133_, v_val_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Option_bind(lean_object* v_00_u03b1_137_, lean_object* v_00_u03b2_138_, lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
lean_object* v___x_141_; 
lean_dec_ref(v_x_140_);
v___x_141_ = lean_box(0);
return v___x_141_;
}
else
{
lean_object* v_val_142_; lean_object* v___x_143_; 
v_val_142_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_val_142_);
lean_dec_ref_known(v_x_139_, 1);
v___x_143_ = lean_apply_1(v_x_140_, v_val_142_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_Option_bindM___redArg(lean_object* v_inst_144_, lean_object* v_f_145_, lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_f_145_);
v___x_147_ = lean_box(0);
v___x_148_ = lean_apply_2(v_inst_144_, lean_box(0), v___x_147_);
return v___x_148_;
}
else
{
lean_object* v_val_149_; lean_object* v___x_150_; 
lean_dec(v_inst_144_);
v_val_149_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_val_149_);
lean_dec_ref_known(v_x_146_, 1);
v___x_150_ = lean_apply_1(v_f_145_, v_val_149_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Option_bindM(lean_object* v_m_151_, lean_object* v_00_u03b1_152_, lean_object* v_00_u03b2_153_, lean_object* v_inst_154_, lean_object* v_f_155_, lean_object* v_x_156_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_f_155_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_apply_2(v_inst_154_, lean_box(0), v___x_157_);
return v___x_158_;
}
else
{
lean_object* v_val_159_; lean_object* v___x_160_; 
lean_dec(v_inst_154_);
v_val_159_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_val_159_);
lean_dec_ref_known(v_x_156_, 1);
v___x_160_ = lean_apply_1(v_f_155_, v_val_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Option_mapM___redArg___lam__0(lean_object* v_val_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_162_, 0, v_val_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Option_mapM___redArg(lean_object* v_inst_164_, lean_object* v_f_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_object* v_toPure_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_f_165_);
v_toPure_167_ = lean_ctor_get(v_inst_164_, 1);
lean_inc(v_toPure_167_);
lean_dec_ref(v_inst_164_);
v___x_168_ = lean_box(0);
v___x_169_ = lean_apply_2(v_toPure_167_, lean_box(0), v___x_168_);
return v___x_169_;
}
else
{
lean_object* v_toFunctor_170_; lean_object* v_val_171_; lean_object* v_map_172_; lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_toFunctor_170_ = lean_ctor_get(v_inst_164_, 0);
lean_inc_ref(v_toFunctor_170_);
lean_dec_ref(v_inst_164_);
v_val_171_ = lean_ctor_get(v_x_166_, 0);
lean_inc(v_val_171_);
lean_dec_ref_known(v_x_166_, 1);
v_map_172_ = lean_ctor_get(v_toFunctor_170_, 0);
lean_inc(v_map_172_);
lean_dec_ref(v_toFunctor_170_);
v___f_173_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_174_ = lean_apply_1(v_f_165_, v_val_171_);
v___x_175_ = lean_apply_4(v_map_172_, lean_box(0), lean_box(0), v___f_173_, v___x_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Option_mapM(lean_object* v_m_176_, lean_object* v_00_u03b1_177_, lean_object* v_00_u03b2_178_, lean_object* v_inst_179_, lean_object* v_f_180_, lean_object* v_x_181_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v_toPure_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_f_180_);
v_toPure_182_ = lean_ctor_get(v_inst_179_, 1);
lean_inc(v_toPure_182_);
lean_dec_ref(v_inst_179_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_apply_2(v_toPure_182_, lean_box(0), v___x_183_);
return v___x_184_;
}
else
{
lean_object* v_toFunctor_185_; lean_object* v_val_186_; lean_object* v_map_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_toFunctor_185_ = lean_ctor_get(v_inst_179_, 0);
lean_inc_ref(v_toFunctor_185_);
lean_dec_ref(v_inst_179_);
v_val_186_ = lean_ctor_get(v_x_181_, 0);
lean_inc(v_val_186_);
lean_dec_ref_known(v_x_181_, 1);
v_map_187_ = lean_ctor_get(v_toFunctor_185_, 0);
lean_inc(v_map_187_);
lean_dec_ref(v_toFunctor_185_);
v___f_188_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_189_ = lean_apply_1(v_f_180_, v_val_186_);
v___x_190_ = lean_apply_4(v_map_187_, lean_box(0), lean_box(0), v___f_188_, v___x_189_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Option_mapA___redArg(lean_object* v_inst_191_, lean_object* v_f_192_, lean_object* v_a_193_){
_start:
{
if (lean_obj_tag(v_a_193_) == 0)
{
lean_object* v_toPure_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v_f_192_);
v_toPure_194_ = lean_ctor_get(v_inst_191_, 1);
lean_inc(v_toPure_194_);
lean_dec_ref(v_inst_191_);
v___x_195_ = lean_box(0);
v___x_196_ = lean_apply_2(v_toPure_194_, lean_box(0), v___x_195_);
return v___x_196_;
}
else
{
lean_object* v_toFunctor_197_; lean_object* v_val_198_; lean_object* v_map_199_; lean_object* v___f_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_toFunctor_197_ = lean_ctor_get(v_inst_191_, 0);
lean_inc_ref(v_toFunctor_197_);
lean_dec_ref(v_inst_191_);
v_val_198_ = lean_ctor_get(v_a_193_, 0);
lean_inc(v_val_198_);
lean_dec_ref_known(v_a_193_, 1);
v_map_199_ = lean_ctor_get(v_toFunctor_197_, 0);
lean_inc(v_map_199_);
lean_dec_ref(v_toFunctor_197_);
v___f_200_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_201_ = lean_apply_1(v_f_192_, v_val_198_);
v___x_202_ = lean_apply_4(v_map_199_, lean_box(0), lean_box(0), v___f_200_, v___x_201_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Option_mapA(lean_object* v_m_203_, lean_object* v_00_u03b1_204_, lean_object* v_00_u03b2_205_, lean_object* v_inst_206_, lean_object* v_f_207_, lean_object* v_a_208_){
_start:
{
if (lean_obj_tag(v_a_208_) == 0)
{
lean_object* v_toPure_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec(v_f_207_);
v_toPure_209_ = lean_ctor_get(v_inst_206_, 1);
lean_inc(v_toPure_209_);
lean_dec_ref(v_inst_206_);
v___x_210_ = lean_box(0);
v___x_211_ = lean_apply_2(v_toPure_209_, lean_box(0), v___x_210_);
return v___x_211_;
}
else
{
lean_object* v_toFunctor_212_; lean_object* v_val_213_; lean_object* v_map_214_; lean_object* v___f_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_toFunctor_212_ = lean_ctor_get(v_inst_206_, 0);
lean_inc_ref(v_toFunctor_212_);
lean_dec_ref(v_inst_206_);
v_val_213_ = lean_ctor_get(v_a_208_, 0);
lean_inc(v_val_213_);
lean_dec_ref_known(v_a_208_, 1);
v_map_214_ = lean_ctor_get(v_toFunctor_212_, 0);
lean_inc(v_map_214_);
lean_dec_ref(v_toFunctor_212_);
v___f_215_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_216_ = lean_apply_1(v_f_207_, v_val_213_);
v___x_217_ = lean_apply_4(v_map_214_, lean_box(0), lean_box(0), v___f_215_, v___x_216_);
return v___x_217_;
}
}
}
lean_object* l_Option_filterM___redArg___lam__0(lean_object* v_x_218_, uint8_t v_b_219_){
_start:
{
if (v_b_219_ == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_box(0);
return v___x_220_;
}
else
{
lean_inc(v_x_218_);
return v_x_218_;
}
}
}
LEAN_EXPORT void l_Option_filterM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_218_ = stack[0].m_obj;
uint8_t v_b_219_ = stack[1].m_num;
lean_object* v_res_221_;
v_res_221_ = l_Option_filterM___redArg___lam__0(v_x_218_, v_b_219_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l_Option_filterM___redArg___lam__0___boxed(lean_object* v_x_222_, lean_object* v_b_223_){
_start:
{
uint8_t v_b_boxed_224_; lean_object* v_res_225_; 
v_b_boxed_224_ = lean_unbox(v_b_223_);
v_res_225_ = l_Option_filterM___redArg___lam__0(v_x_222_, v_b_boxed_224_);
lean_dec(v_x_222_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Option_filterM___redArg(lean_object* v_inst_226_, lean_object* v_p_227_, lean_object* v_x_228_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
lean_object* v_toPure_229_; lean_object* v___x_230_; 
lean_dec(v_p_227_);
v_toPure_229_ = lean_ctor_get(v_inst_226_, 1);
lean_inc(v_toPure_229_);
lean_dec_ref(v_inst_226_);
v___x_230_ = lean_apply_2(v_toPure_229_, lean_box(0), v_x_228_);
return v___x_230_;
}
else
{
lean_object* v_toFunctor_231_; lean_object* v_val_232_; lean_object* v_map_233_; lean_object* v___f_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_toFunctor_231_ = lean_ctor_get(v_inst_226_, 0);
lean_inc_ref(v_toFunctor_231_);
lean_dec_ref(v_inst_226_);
v_val_232_ = lean_ctor_get(v_x_228_, 0);
lean_inc(v_val_232_);
v_map_233_ = lean_ctor_get(v_toFunctor_231_, 0);
lean_inc(v_map_233_);
lean_dec_ref(v_toFunctor_231_);
v___f_234_ = lean_alloc_closure((void*)(l_Option_filterM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_234_, 0, v_x_228_);
v___x_235_ = lean_apply_1(v_p_227_, v_val_232_);
v___x_236_ = lean_apply_4(v_map_233_, lean_box(0), lean_box(0), v___f_234_, v___x_235_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Option_filterM(lean_object* v_m_237_, lean_object* v_00_u03b1_238_, lean_object* v_inst_239_, lean_object* v_p_240_, lean_object* v_x_241_){
_start:
{
if (lean_obj_tag(v_x_241_) == 0)
{
lean_object* v_toPure_242_; lean_object* v___x_243_; 
lean_dec(v_p_240_);
v_toPure_242_ = lean_ctor_get(v_inst_239_, 1);
lean_inc(v_toPure_242_);
lean_dec_ref(v_inst_239_);
v___x_243_ = lean_apply_2(v_toPure_242_, lean_box(0), v_x_241_);
return v___x_243_;
}
else
{
lean_object* v_toFunctor_244_; lean_object* v_val_245_; lean_object* v_map_246_; lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_toFunctor_244_ = lean_ctor_get(v_inst_239_, 0);
lean_inc_ref(v_toFunctor_244_);
lean_dec_ref(v_inst_239_);
v_val_245_ = lean_ctor_get(v_x_241_, 0);
lean_inc(v_val_245_);
v_map_246_ = lean_ctor_get(v_toFunctor_244_, 0);
lean_inc(v_map_246_);
lean_dec_ref(v_toFunctor_244_);
v___f_247_ = lean_alloc_closure((void*)(l_Option_filterM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_247_, 0, v_x_241_);
v___x_248_ = lean_apply_1(v_p_240_, v_val_245_);
v___x_249_ = lean_apply_4(v_map_246_, lean_box(0), lean_box(0), v___f_247_, v___x_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Option_filter___redArg(lean_object* v_p_250_, lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
lean_dec_ref(v_p_250_);
return v_x_251_;
}
else
{
lean_object* v_val_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v_val_252_ = lean_ctor_get(v_x_251_, 0);
lean_inc(v_val_252_);
v___x_253_ = lean_apply_1(v_p_250_, v_val_252_);
v___x_254_ = lean_unbox(v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec_ref_known(v_x_251_, 1);
v___x_255_ = lean_box(0);
return v___x_255_;
}
else
{
return v_x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_filter(lean_object* v_00_u03b1_256_, lean_object* v_p_257_, lean_object* v_x_258_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
lean_dec_ref(v_p_257_);
return v_x_258_;
}
else
{
lean_object* v_val_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v_val_259_ = lean_ctor_get(v_x_258_, 0);
lean_inc(v_val_259_);
v___x_260_ = lean_apply_1(v_p_257_, v_val_259_);
v___x_261_ = lean_unbox(v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_dec_ref_known(v_x_258_, 1);
v___x_262_ = lean_box(0);
return v___x_262_;
}
else
{
return v_x_258_;
}
}
}
}
uint8_t l_Option_all___redArg(lean_object* v_p_263_, lean_object* v_x_264_){
_start:
{
if (lean_obj_tag(v_x_264_) == 0)
{
uint8_t v___x_265_; 
lean_dec_ref(v_p_263_);
v___x_265_ = 1;
return v___x_265_;
}
else
{
lean_object* v_val_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_val_266_ = lean_ctor_get(v_x_264_, 0);
lean_inc(v_val_266_);
lean_dec_ref_known(v_x_264_, 1);
v___x_267_ = lean_apply_1(v_p_263_, v_val_266_);
v___x_268_ = lean_unbox(v___x_267_);
return v___x_268_;
}
}
}
LEAN_EXPORT void l_Option_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_263_ = stack[0].m_obj;
lean_object* v_x_264_ = stack[1].m_obj;
uint8_t v_res_269_;
v_res_269_ = l_Option_all___redArg(v_p_263_, v_x_264_);
stack->m_num = v_res_269_;
}
LEAN_EXPORT lean_object* l_Option_all___redArg___boxed(lean_object* v_p_270_, lean_object* v_x_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l_Option_all___redArg(v_p_270_, v_x_271_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
uint8_t l_Option_all(lean_object* v_00_u03b1_274_, lean_object* v_p_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
uint8_t v___x_277_; 
lean_dec_ref(v_p_275_);
v___x_277_ = 1;
return v___x_277_;
}
else
{
lean_object* v_val_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_val_278_ = lean_ctor_get(v_x_276_, 0);
lean_inc(v_val_278_);
lean_dec_ref_known(v_x_276_, 1);
v___x_279_ = lean_apply_1(v_p_275_, v_val_278_);
v___x_280_ = lean_unbox(v___x_279_);
return v___x_280_;
}
}
}
LEAN_EXPORT void l_Option_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_275_ = stack[1].m_obj;
lean_object* v_x_276_ = stack[2].m_obj;
uint8_t v_res_281_;
v_res_281_ = l_Option_all(lean_box(0), v_p_275_, v_x_276_);
stack->m_num = v_res_281_;
}
LEAN_EXPORT lean_object* l_Option_all___boxed(lean_object* v_00_u03b1_282_, lean_object* v_p_283_, lean_object* v_x_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Option_all(v_00_u03b1_282_, v_p_283_, v_x_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
uint8_t l_Option_any___redArg(lean_object* v_p_287_, lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_288_) == 0)
{
uint8_t v___x_289_; 
lean_dec_ref(v_p_287_);
v___x_289_ = 0;
return v___x_289_;
}
else
{
lean_object* v_val_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v_val_290_ = lean_ctor_get(v_x_288_, 0);
lean_inc(v_val_290_);
lean_dec_ref_known(v_x_288_, 1);
v___x_291_ = lean_apply_1(v_p_287_, v_val_290_);
v___x_292_ = lean_unbox(v___x_291_);
return v___x_292_;
}
}
}
LEAN_EXPORT void l_Option_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_287_ = stack[0].m_obj;
lean_object* v_x_288_ = stack[1].m_obj;
uint8_t v_res_293_;
v_res_293_ = l_Option_any___redArg(v_p_287_, v_x_288_);
stack->m_num = v_res_293_;
}
LEAN_EXPORT lean_object* l_Option_any___redArg___boxed(lean_object* v_p_294_, lean_object* v_x_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Option_any___redArg(v_p_294_, v_x_295_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
uint8_t l_Option_any(lean_object* v_00_u03b1_298_, lean_object* v_p_299_, lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
uint8_t v___x_301_; 
lean_dec_ref(v_p_299_);
v___x_301_ = 0;
return v___x_301_;
}
else
{
lean_object* v_val_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_val_302_ = lean_ctor_get(v_x_300_, 0);
lean_inc(v_val_302_);
lean_dec_ref_known(v_x_300_, 1);
v___x_303_ = lean_apply_1(v_p_299_, v_val_302_);
v___x_304_ = lean_unbox(v___x_303_);
return v___x_304_;
}
}
}
LEAN_EXPORT void l_Option_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_299_ = stack[1].m_obj;
lean_object* v_x_300_ = stack[2].m_obj;
uint8_t v_res_305_;
v_res_305_ = l_Option_any(lean_box(0), v_p_299_, v_x_300_);
stack->m_num = v_res_305_;
}
LEAN_EXPORT lean_object* l_Option_any___boxed(lean_object* v_00_u03b1_306_, lean_object* v_p_307_, lean_object* v_x_308_){
_start:
{
uint8_t v_res_309_; lean_object* v_r_310_; 
v_res_309_ = l_Option_any(v_00_u03b1_306_, v_p_307_, v_x_308_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg___lam__0(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_box(0);
v___x_314_ = lean_apply_1(v_x_312_, v___x_313_);
return v___x_314_;
}
else
{
lean_dec_ref(v_x_312_);
lean_inc_ref(v_x_311_);
return v_x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg___lam__0___boxed(lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Option_instOrElse___redArg___lam__0(v_x_315_, v_x_316_);
lean_dec(v_x_315_);
return v_res_317_;
}
}
lean_object* l_Option_instOrElse___redArg(){
_start:
{
lean_object* v___f_320_; 
v___f_320_ = ((lean_object*)(l_Option_instOrElse___redArg___closed__0));
return v___f_320_;
}
}
LEAN_EXPORT void l_Option_instOrElse___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_321_;
v_res_321_ = l_Option_instOrElse___redArg();
stack->m_obj
 = v_res_321_;
}
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg___boxed(lean_object* v___dummy_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Option_instOrElse___redArg();
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse(lean_object* v_00_u03b1_324_){
_start:
{
lean_object* v___f_325_; 
v___f_325_ = ((lean_object*)(l_Option_instOrElse___redArg___closed__0));
return v___f_325_;
}
}
uint8_t l_Option_instDecidableRelLt___redArg(lean_object* v_s_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
lean_dec_ref(v_s_326_);
if (lean_obj_tag(v_x_328_) == 0)
{
uint8_t v___x_329_; 
v___x_329_ = 0;
return v___x_329_;
}
else
{
uint8_t v___x_330_; 
lean_dec_ref_known(v_x_328_, 1);
v___x_330_ = 1;
return v___x_330_;
}
}
else
{
if (lean_obj_tag(v_x_328_) == 0)
{
uint8_t v___x_331_; 
lean_dec_ref_known(v_x_327_, 1);
lean_dec_ref(v_s_326_);
v___x_331_ = 0;
return v___x_331_;
}
else
{
lean_object* v_val_332_; lean_object* v_val_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_val_332_ = lean_ctor_get(v_x_327_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v_x_327_, 1);
v_val_333_ = lean_ctor_get(v_x_328_, 0);
lean_inc(v_val_333_);
lean_dec_ref_known(v_x_328_, 1);
v___x_334_ = lean_apply_2(v_s_326_, v_val_332_, v_val_333_);
v___x_335_ = lean_unbox(v___x_334_);
return v___x_335_;
}
}
}
}
LEAN_EXPORT void l_Option_instDecidableRelLt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_326_ = stack[0].m_obj;
lean_object* v_x_327_ = stack[1].m_obj;
lean_object* v_x_328_ = stack[2].m_obj;
uint8_t v_res_336_;
v_res_336_ = l_Option_instDecidableRelLt___redArg(v_s_326_, v_x_327_, v_x_328_);
stack->m_num = v_res_336_;
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___redArg___boxed(lean_object* v_s_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_Option_instDecidableRelLt___redArg(v_s_337_, v_x_338_, v_x_339_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
uint8_t l_Option_instDecidableRelLt(lean_object* v_00_u03b1_342_, lean_object* v_00_u03b2_343_, lean_object* v_r_344_, lean_object* v_s_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
uint8_t v___x_348_; 
v___x_348_ = l_Option_instDecidableRelLt___redArg(v_s_345_, v_x_346_, v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT void l_Option_instDecidableRelLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_345_ = stack[3].m_obj;
lean_object* v_x_346_ = stack[4].m_obj;
lean_object* v_x_347_ = stack[5].m_obj;
uint8_t v_res_349_;
v_res_349_ = l_Option_instDecidableRelLt(lean_box(0), lean_box(0), lean_box(0), v_s_345_, v_x_346_, v_x_347_);
stack->m_num = v_res_349_;
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___boxed(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_r_352_, lean_object* v_s_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Option_instDecidableRelLt(v_00_u03b1_350_, v_00_u03b2_351_, v_r_352_, v_s_353_, v_x_354_, v_x_355_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
uint8_t l_Option_instDecidableRelLe___redArg(lean_object* v_s_358_, lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_x_359_) == 0)
{
uint8_t v___x_361_; 
lean_dec(v_x_360_);
lean_dec_ref(v_s_358_);
v___x_361_ = 1;
return v___x_361_;
}
else
{
if (lean_obj_tag(v_x_360_) == 0)
{
uint8_t v___x_362_; 
lean_dec_ref_known(v_x_359_, 1);
lean_dec_ref(v_s_358_);
v___x_362_ = 0;
return v___x_362_;
}
else
{
lean_object* v_val_363_; lean_object* v_val_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_val_363_ = lean_ctor_get(v_x_359_, 0);
lean_inc(v_val_363_);
lean_dec_ref_known(v_x_359_, 1);
v_val_364_ = lean_ctor_get(v_x_360_, 0);
lean_inc(v_val_364_);
lean_dec_ref_known(v_x_360_, 1);
v___x_365_ = lean_apply_2(v_s_358_, v_val_363_, v_val_364_);
v___x_366_ = lean_unbox(v___x_365_);
return v___x_366_;
}
}
}
}
LEAN_EXPORT void l_Option_instDecidableRelLe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_358_ = stack[0].m_obj;
lean_object* v_x_359_ = stack[1].m_obj;
lean_object* v_x_360_ = stack[2].m_obj;
uint8_t v_res_367_;
v_res_367_ = l_Option_instDecidableRelLe___redArg(v_s_358_, v_x_359_, v_x_360_);
stack->m_num = v_res_367_;
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLe___redArg___boxed(lean_object* v_s_368_, lean_object* v_x_369_, lean_object* v_x_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l_Option_instDecidableRelLe___redArg(v_s_368_, v_x_369_, v_x_370_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
uint8_t l_Option_instDecidableRelLe(lean_object* v_00_u03b1_373_, lean_object* v_00_u03b2_374_, lean_object* v_r_375_, lean_object* v_s_376_, lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = l_Option_instDecidableRelLe___redArg(v_s_376_, v_x_377_, v_x_378_);
return v___x_379_;
}
}
LEAN_EXPORT void l_Option_instDecidableRelLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_376_ = stack[3].m_obj;
lean_object* v_x_377_ = stack[4].m_obj;
lean_object* v_x_378_ = stack[5].m_obj;
uint8_t v_res_380_;
v_res_380_ = l_Option_instDecidableRelLe(lean_box(0), lean_box(0), lean_box(0), v_s_376_, v_x_377_, v_x_378_);
stack->m_num = v_res_380_;
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLe___boxed(lean_object* v_00_u03b1_381_, lean_object* v_00_u03b2_382_, lean_object* v_r_383_, lean_object* v_s_384_, lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
uint8_t v_res_387_; lean_object* v_r_388_; 
v_res_387_ = l_Option_instDecidableRelLe(v_00_u03b1_381_, v_00_u03b2_382_, v_r_383_, v_s_384_, v_x_385_, v_x_386_);
v_r_388_ = lean_box(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT lean_object* l_Option_merge___redArg(lean_object* v_fn_389_, lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_dec(v_fn_389_);
return v_x_391_;
}
else
{
if (lean_obj_tag(v_x_391_) == 0)
{
lean_dec(v_fn_389_);
return v_x_390_;
}
else
{
lean_object* v_val_392_; lean_object* v_val_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_val_392_ = lean_ctor_get(v_x_390_, 0);
lean_inc(v_val_392_);
lean_dec_ref_known(v_x_390_, 1);
v_val_393_ = lean_ctor_get(v_x_391_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_x_391_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v_x_391_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_val_393_);
lean_dec(v_x_391_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_apply_2(v_fn_389_, v_val_392_, v_val_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_merge(lean_object* v_00_u03b1_402_, lean_object* v_fn_403_, lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Option_merge___redArg(v_fn_403_, v_x_404_, v_x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Option_elim___redArg(lean_object* v_x_407_, lean_object* v_x_408_, lean_object* v_x_409_){
_start:
{
if (lean_obj_tag(v_x_407_) == 0)
{
lean_dec(v_x_409_);
lean_inc(v_x_408_);
return v_x_408_;
}
else
{
lean_object* v_val_410_; lean_object* v___x_411_; 
v_val_410_ = lean_ctor_get(v_x_407_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v_x_407_, 1);
v___x_411_ = lean_apply_1(v_x_409_, v_val_410_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elim___redArg___boxed(lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Option_elim___redArg(v_x_412_, v_x_413_, v_x_414_);
lean_dec(v_x_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Option_elim(lean_object* v_00_u03b1_416_, lean_object* v_00_u03b2_417_, lean_object* v_x_418_, lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
if (lean_obj_tag(v_x_418_) == 0)
{
lean_dec(v_x_420_);
lean_inc(v_x_419_);
return v_x_419_;
}
else
{
lean_object* v_val_421_; lean_object* v___x_422_; 
v_val_421_ = lean_ctor_get(v_x_418_, 0);
lean_inc(v_val_421_);
lean_dec_ref_known(v_x_418_, 1);
v___x_422_ = lean_apply_1(v_x_420_, v_val_421_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elim___boxed(lean_object* v_00_u03b1_423_, lean_object* v_00_u03b2_424_, lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Option_elim(v_00_u03b1_423_, v_00_u03b2_424_, v_x_425_, v_x_426_, v_x_427_);
lean_dec(v_x_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Option_get___redArg(lean_object* v_x_429_){
_start:
{
lean_object* v_val_430_; 
v_val_430_ = lean_ctor_get(v_x_429_, 0);
lean_inc(v_val_430_);
return v_val_430_;
}
}
LEAN_EXPORT lean_object* l_Option_get___redArg___boxed(lean_object* v_x_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Option_get___redArg(v_x_431_);
lean_dec(v_x_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Option_get(lean_object* v_00_u03b1_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v_val_436_; 
v_val_436_ = lean_ctor_get(v_x_434_, 0);
lean_inc(v_val_436_);
return v_val_436_;
}
}
LEAN_EXPORT lean_object* l_Option_get___boxed(lean_object* v_00_u03b1_437_, lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Option_get(v_00_u03b1_437_, v_x_438_, v_x_439_);
lean_dec(v_x_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Option_guard___redArg(lean_object* v_p_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_443_; uint8_t v___x_444_; 
lean_inc(v_a_442_);
v___x_443_ = lean_apply_1(v_p_441_, v_a_442_);
v___x_444_ = lean_unbox(v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_dec(v_a_442_);
v___x_445_ = lean_box(0);
return v___x_445_;
}
else
{
lean_object* v___x_446_; 
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v_a_442_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Option_guard(lean_object* v_00_u03b1_447_, lean_object* v_p_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_450_; uint8_t v___x_451_; 
lean_inc(v_a_449_);
v___x_450_ = lean_apply_1(v_p_448_, v_a_449_);
v___x_451_ = lean_unbox(v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_dec(v_a_449_);
v___x_452_ = lean_box(0);
return v___x_452_;
}
else
{
lean_object* v___x_453_; 
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v_a_449_);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toList___redArg(lean_object* v_x_454_){
_start:
{
if (lean_obj_tag(v_x_454_) == 0)
{
lean_object* v___x_455_; 
v___x_455_ = lean_box(0);
return v___x_455_;
}
else
{
lean_object* v_val_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_val_456_ = lean_ctor_get(v_x_454_, 0);
v___x_457_ = lean_box(0);
lean_inc(v_val_456_);
v___x_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_458_, 0, v_val_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toList___redArg___boxed(lean_object* v_x_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Option_toList___redArg(v_x_459_);
lean_dec(v_x_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Option_toList(lean_object* v_00_u03b1_461_, lean_object* v_x_462_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
lean_object* v___x_463_; 
v___x_463_ = lean_box(0);
return v___x_463_;
}
else
{
lean_object* v_val_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_val_464_ = lean_ctor_get(v_x_462_, 0);
v___x_465_ = lean_box(0);
lean_inc(v_val_464_);
v___x_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_466_, 0, v_val_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toList___boxed(lean_object* v_00_u03b1_467_, lean_object* v_x_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Option_toList(v_00_u03b1_467_, v_x_468_);
lean_dec(v_x_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Option_toArray___redArg(lean_object* v_x_472_){
_start:
{
if (lean_obj_tag(v_x_472_) == 0)
{
lean_object* v___x_473_; 
v___x_473_ = ((lean_object*)(l_Option_toArray___redArg___closed__0));
return v___x_473_;
}
else
{
lean_object* v_val_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_val_474_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_val_474_);
lean_dec_ref_known(v_x_472_, 1);
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = lean_mk_empty_array_with_capacity(v___x_475_);
v___x_477_ = lean_array_push(v___x_476_, v_val_474_);
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toArray(lean_object* v_00_u03b1_478_, lean_object* v_x_479_){
_start:
{
if (lean_obj_tag(v_x_479_) == 0)
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l_Option_toArray___redArg___closed__0));
return v___x_480_;
}
else
{
lean_object* v_val_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_val_481_ = lean_ctor_get(v_x_479_, 0);
lean_inc(v_val_481_);
lean_dec_ref_known(v_x_479_, 1);
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_mk_empty_array_with_capacity(v___x_482_);
v___x_484_ = lean_array_push(v___x_483_, v_val_481_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l_Option_join___redArg(lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
lean_object* v___x_486_; 
v___x_486_ = lean_box(0);
return v___x_486_;
}
else
{
lean_object* v_val_487_; 
v_val_487_ = lean_ctor_get(v_x_485_, 0);
lean_inc(v_val_487_);
return v_val_487_;
}
}
}
LEAN_EXPORT lean_object* l_Option_join___redArg___boxed(lean_object* v_x_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Option_join___redArg(v_x_488_);
lean_dec(v_x_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Option_join(lean_object* v_00_u03b1_490_, lean_object* v_x_491_){
_start:
{
if (lean_obj_tag(v_x_491_) == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_box(0);
return v___x_492_;
}
else
{
lean_object* v_val_493_; 
v_val_493_ = lean_ctor_get(v_x_491_, 0);
lean_inc(v_val_493_);
return v_val_493_;
}
}
}
LEAN_EXPORT lean_object* l_Option_join___boxed(lean_object* v_00_u03b1_494_, lean_object* v_x_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Option_join(v_00_u03b1_494_, v_x_495_);
lean_dec(v_x_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Option_sequence___redArg(lean_object* v_inst_497_, lean_object* v_x_498_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v_toPure_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_toPure_499_ = lean_ctor_get(v_inst_497_, 1);
lean_inc(v_toPure_499_);
lean_dec_ref(v_inst_497_);
v___x_500_ = lean_box(0);
v___x_501_ = lean_apply_2(v_toPure_499_, lean_box(0), v___x_500_);
return v___x_501_;
}
else
{
lean_object* v_toFunctor_502_; lean_object* v_val_503_; lean_object* v_map_504_; lean_object* v___f_505_; lean_object* v___x_506_; 
v_toFunctor_502_ = lean_ctor_get(v_inst_497_, 0);
lean_inc_ref(v_toFunctor_502_);
lean_dec_ref(v_inst_497_);
v_val_503_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_x_498_, 1);
v_map_504_ = lean_ctor_get(v_toFunctor_502_, 0);
lean_inc(v_map_504_);
lean_dec_ref(v_toFunctor_502_);
v___f_505_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_506_ = lean_apply_4(v_map_504_, lean_box(0), lean_box(0), v___f_505_, v_val_503_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l_Option_sequence(lean_object* v_m_507_, lean_object* v_inst_508_, lean_object* v_00_u03b1_509_, lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
lean_object* v_toPure_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_toPure_511_ = lean_ctor_get(v_inst_508_, 1);
lean_inc(v_toPure_511_);
lean_dec_ref(v_inst_508_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_apply_2(v_toPure_511_, lean_box(0), v___x_512_);
return v___x_513_;
}
else
{
lean_object* v_toFunctor_514_; lean_object* v_val_515_; lean_object* v_map_516_; lean_object* v___f_517_; lean_object* v___x_518_; 
v_toFunctor_514_ = lean_ctor_get(v_inst_508_, 0);
lean_inc_ref(v_toFunctor_514_);
lean_dec_ref(v_inst_508_);
v_val_515_ = lean_ctor_get(v_x_510_, 0);
lean_inc(v_val_515_);
lean_dec_ref_known(v_x_510_, 1);
v_map_516_ = lean_ctor_get(v_toFunctor_514_, 0);
lean_inc(v_map_516_);
lean_dec_ref(v_toFunctor_514_);
v___f_517_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_518_ = lean_apply_4(v_map_516_, lean_box(0), lean_box(0), v___f_517_, v_val_515_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elimM___redArg___lam__0(lean_object* v_y_519_, lean_object* v_z_520_, lean_object* v_____do__lift_521_){
_start:
{
if (lean_obj_tag(v_____do__lift_521_) == 0)
{
lean_dec(v_z_520_);
lean_inc(v_y_519_);
return v_y_519_;
}
else
{
lean_object* v_val_522_; lean_object* v___x_523_; 
v_val_522_ = lean_ctor_get(v_____do__lift_521_, 0);
lean_inc(v_val_522_);
lean_dec_ref_known(v_____do__lift_521_, 1);
v___x_523_ = lean_apply_1(v_z_520_, v_val_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elimM___redArg___lam__0___boxed(lean_object* v_y_524_, lean_object* v_z_525_, lean_object* v_____do__lift_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Option_elimM___redArg___lam__0(v_y_524_, v_z_525_, v_____do__lift_526_);
lean_dec(v_y_524_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Option_elimM___redArg(lean_object* v_inst_528_, lean_object* v_x_529_, lean_object* v_y_530_, lean_object* v_z_531_){
_start:
{
lean_object* v_toBind_532_; lean_object* v___f_533_; lean_object* v___x_534_; 
v_toBind_532_ = lean_ctor_get(v_inst_528_, 1);
lean_inc(v_toBind_532_);
lean_dec_ref(v_inst_528_);
v___f_533_ = lean_alloc_closure((void*)(l_Option_elimM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_533_, 0, v_y_530_);
lean_closure_set(v___f_533_, 1, v_z_531_);
v___x_534_ = lean_apply_4(v_toBind_532_, lean_box(0), lean_box(0), v_x_529_, v___f_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Option_elimM(lean_object* v_m_535_, lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_inst_538_, lean_object* v_x_539_, lean_object* v_y_540_, lean_object* v_z_541_){
_start:
{
lean_object* v_toBind_542_; lean_object* v___f_543_; lean_object* v___x_544_; 
v_toBind_542_ = lean_ctor_get(v_inst_538_, 1);
lean_inc(v_toBind_542_);
lean_dec_ref(v_inst_538_);
v___f_543_ = lean_alloc_closure((void*)(l_Option_elimM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_543_, 0, v_y_540_);
lean_closure_set(v___f_543_, 1, v_z_541_);
v___x_544_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v_x_539_, v___f_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Option_getDM___redArg(lean_object* v_inst_545_, lean_object* v_x_546_, lean_object* v_y_547_){
_start:
{
if (lean_obj_tag(v_x_546_) == 0)
{
lean_dec(v_inst_545_);
lean_inc(v_y_547_);
return v_y_547_;
}
else
{
lean_object* v_val_548_; lean_object* v___x_549_; 
v_val_548_ = lean_ctor_get(v_x_546_, 0);
lean_inc(v_val_548_);
lean_dec_ref_known(v_x_546_, 1);
v___x_549_ = lean_apply_2(v_inst_545_, lean_box(0), v_val_548_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Option_getDM___redArg___boxed(lean_object* v_inst_550_, lean_object* v_x_551_, lean_object* v_y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Option_getDM___redArg(v_inst_550_, v_x_551_, v_y_552_);
lean_dec(v_y_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Option_getDM(lean_object* v_m_554_, lean_object* v_00_u03b1_555_, lean_object* v_inst_556_, lean_object* v_x_557_, lean_object* v_y_558_){
_start:
{
if (lean_obj_tag(v_x_557_) == 0)
{
lean_dec(v_inst_556_);
lean_inc(v_y_558_);
return v_y_558_;
}
else
{
lean_object* v_val_559_; lean_object* v___x_560_; 
v_val_559_ = lean_ctor_get(v_x_557_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v_x_557_, 1);
v___x_560_ = lean_apply_2(v_inst_556_, lean_box(0), v_val_559_);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l_Option_getDM___boxed(lean_object* v_m_561_, lean_object* v_00_u03b1_562_, lean_object* v_inst_563_, lean_object* v_x_564_, lean_object* v_y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Option_getDM(v_m_561_, v_00_u03b1_562_, v_inst_563_, v_x_564_, v_y_565_);
lean_dec(v_y_565_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Option_min___redArg(lean_object* v_inst_567_, lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_dec(v_inst_567_);
if (lean_obj_tag(v_x_569_) == 0)
{
return v_x_569_;
}
else
{
lean_dec_ref_known(v_x_569_, 1);
return v_x_568_;
}
}
else
{
if (lean_obj_tag(v_x_569_) == 0)
{
lean_dec_ref_known(v_x_568_, 1);
lean_dec(v_inst_567_);
return v_x_569_;
}
else
{
lean_object* v_val_570_; lean_object* v_val_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
v_val_570_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_val_570_);
lean_dec_ref_known(v_x_568_, 1);
v_val_571_ = lean_ctor_get(v_x_569_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_x_569_);
if (v_isSharedCheck_579_ == 0)
{
v___x_573_ = v_x_569_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_val_571_);
lean_dec(v_x_569_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_575_ = lean_apply_2(v_inst_567_, v_val_570_, v_val_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_min(lean_object* v_00_u03b1_580_, lean_object* v_inst_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Option_min___redArg(v_inst_581_, v_x_582_, v_x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Option_instMin___redArg(lean_object* v_inst_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = lean_alloc_closure((void*)(l_Option_min), 4, 2);
lean_closure_set(v___x_586_, 0, lean_box(0));
lean_closure_set(v___x_586_, 1, v_inst_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Option_instMin(lean_object* v_00_u03b1_587_, lean_object* v_inst_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_closure((void*)(l_Option_min), 4, 2);
lean_closure_set(v___x_589_, 0, lean_box(0));
lean_closure_set(v___x_589_, 1, v_inst_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Option_max___redArg(lean_object* v_inst_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
if (lean_obj_tag(v_x_591_) == 0)
{
lean_dec(v_inst_590_);
return v_x_592_;
}
else
{
if (lean_obj_tag(v_x_592_) == 0)
{
lean_dec(v_inst_590_);
return v_x_591_;
}
else
{
lean_object* v_val_593_; lean_object* v_val_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_602_; 
v_val_593_ = lean_ctor_get(v_x_591_, 0);
lean_inc(v_val_593_);
lean_dec_ref_known(v_x_591_, 1);
v_val_594_ = lean_ctor_get(v_x_592_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v_x_592_);
if (v_isSharedCheck_602_ == 0)
{
v___x_596_ = v_x_592_;
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_val_594_);
lean_dec(v_x_592_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_apply_2(v_inst_590_, v_val_593_, v_val_594_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_max(lean_object* v_00_u03b1_603_, lean_object* v_inst_604_, lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Option_max___redArg(v_inst_604_, v_x_605_, v_x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Option_instMax___redArg(lean_object* v_inst_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_closure((void*)(l_Option_max), 4, 2);
lean_closure_set(v___x_609_, 0, lean_box(0));
lean_closure_set(v___x_609_, 1, v_inst_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Option_instMax(lean_object* v_00_u03b1_610_, lean_object* v_inst_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_closure((void*)(l_Option_max), 4, 2);
lean_closure_set(v___x_612_, 0, lean_box(0));
lean_closure_set(v___x_612_, 1, v_inst_611_);
return v___x_612_;
}
}
lean_object* l_instLTOption___redArg(){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = lean_box(0);
return v___x_614_;
}
}
LEAN_EXPORT void l_instLTOption___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_615_;
v_res_615_ = l_instLTOption___redArg();
stack->m_obj
 = v_res_615_;
}
LEAN_EXPORT lean_object* l_instLTOption___redArg___boxed(lean_object* v___dummy_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_instLTOption___redArg();
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_instLTOption(lean_object* v_00_u03b1_618_, lean_object* v_inst_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lean_box(0);
return v___x_620_;
}
}
lean_object* l_instLEOption___redArg(){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = lean_box(0);
return v___x_622_;
}
}
LEAN_EXPORT void l_instLEOption___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_623_;
v_res_623_ = l_instLEOption___redArg();
stack->m_obj
 = v_res_623_;
}
LEAN_EXPORT lean_object* l_instLEOption___redArg___boxed(lean_object* v___dummy_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_instLEOption___redArg();
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_instLEOption(lean_object* v_00_u03b1_626_, lean_object* v_inst_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_box(0);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_instFunctorOption___lam__0(lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
if (lean_obj_tag(v___y_632_) == 0)
{
lean_object* v___x_633_; 
lean_dec(v___y_631_);
v___x_633_ = lean_box(0);
return v___x_633_;
}
else
{
lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_isSharedCheck_640_ = !lean_is_exclusive(v___y_632_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v___y_632_, 0);
lean_dec(v_unused_641_);
v___x_635_ = v___y_632_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_dec(v___y_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___y_631_);
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___y_631_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__0(lean_object* v_00_u03b1_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v___y_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__1(lean_object* v_00_u03b1_651_, lean_object* v_00_u03b2_652_, lean_object* v_f_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_f_653_) == 0)
{
lean_object* v___x_655_; 
lean_dec_ref(v_x_654_);
v___x_655_ = lean_box(0);
return v___x_655_;
}
else
{
lean_object* v_val_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_val_656_ = lean_ctor_get(v_f_653_, 0);
lean_inc(v_val_656_);
lean_dec_ref_known(v_f_653_, 1);
v___x_657_ = lean_box(0);
v___x_658_ = lean_apply_1(v_x_654_, v___x_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v___x_659_; 
lean_dec(v_val_656_);
v___x_659_ = lean_box(0);
return v___x_659_;
}
else
{
lean_object* v_val_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_668_; 
v_val_660_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_668_ == 0)
{
v___x_662_ = v___x_658_;
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_val_660_);
lean_dec(v___x_658_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = lean_apply_1(v_val_656_, v_val_660_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__2(lean_object* v_00_u03b1_669_, lean_object* v_00_u03b2_670_, lean_object* v_x_671_, lean_object* v_y_672_){
_start:
{
if (lean_obj_tag(v_x_671_) == 0)
{
lean_dec_ref(v_y_672_);
return v_x_671_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_box(0);
v___x_674_ = lean_apply_1(v_y_672_, v___x_673_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v___x_675_; 
v___x_675_ = lean_box(0);
return v___x_675_;
}
else
{
lean_dec_ref_known(v___x_674_, 1);
lean_inc_ref(v_x_671_);
return v_x_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__2___boxed(lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_x_678_, lean_object* v_y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_instMonadOption___lam__2(v_00_u03b1_676_, v_00_u03b2_677_, v_x_678_, v_y_679_);
lean_dec(v_x_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__3(lean_object* v_00_u03b1_681_, lean_object* v_00_u03b2_682_, lean_object* v_x_683_, lean_object* v_y_684_){
_start:
{
if (lean_obj_tag(v_x_683_) == 0)
{
lean_object* v___x_685_; 
lean_dec_ref(v_y_684_);
v___x_685_ = lean_box(0);
return v___x_685_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_box(0);
v___x_687_ = lean_apply_1(v_y_684_, v___x_686_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__3___boxed(lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_x_690_, lean_object* v_y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_instMonadOption___lam__3(v_00_u03b1_688_, v_00_u03b2_689_, v_x_690_, v_y_691_);
lean_dec(v_x_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__0(lean_object* v_00_u03b1_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = lean_box(0);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__1(lean_object* v_00_u03b1_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
if (lean_obj_tag(v_x_711_) == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_box(0);
v___x_714_ = lean_apply_1(v_x_712_, v___x_713_);
return v___x_714_;
}
else
{
lean_dec_ref(v_x_712_);
lean_inc_ref(v_x_711_);
return v_x_711_;
}
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__1___boxed(lean_object* v_00_u03b1_715_, lean_object* v_x_716_, lean_object* v_x_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_instAlternativeOption___lam__1(v_00_u03b1_715_, v_x_716_, v_x_717_);
lean_dec(v_x_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_liftOption___redArg(lean_object* v_inst_726_, lean_object* v_x_727_){
_start:
{
if (lean_obj_tag(v_x_727_) == 0)
{
lean_object* v_failure_728_; lean_object* v___x_729_; 
v_failure_728_ = lean_ctor_get(v_inst_726_, 1);
lean_inc(v_failure_728_);
lean_dec_ref(v_inst_726_);
v___x_729_ = lean_apply_1(v_failure_728_, lean_box(0));
return v___x_729_;
}
else
{
lean_object* v_toApplicative_730_; lean_object* v_toPure_731_; lean_object* v_val_732_; lean_object* v___x_733_; 
v_toApplicative_730_ = lean_ctor_get(v_inst_726_, 0);
lean_inc_ref(v_toApplicative_730_);
lean_dec_ref(v_inst_726_);
v_toPure_731_ = lean_ctor_get(v_toApplicative_730_, 1);
lean_inc(v_toPure_731_);
lean_dec_ref(v_toApplicative_730_);
v_val_732_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_val_732_);
lean_dec_ref_known(v_x_727_, 1);
v___x_733_ = lean_apply_2(v_toPure_731_, lean_box(0), v_val_732_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_liftOption(lean_object* v_m_734_, lean_object* v_00_u03b1_735_, lean_object* v_inst_736_, lean_object* v_x_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_liftOption___redArg(v_inst_736_, v_x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___redArg(lean_object* v_x_739_, lean_object* v_handle_740_){
_start:
{
if (lean_obj_tag(v_x_739_) == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_box(0);
v___x_742_ = lean_apply_1(v_handle_740_, v___x_741_);
return v___x_742_;
}
else
{
lean_dec_ref(v_handle_740_);
lean_inc_ref(v_x_739_);
return v_x_739_;
}
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___redArg___boxed(lean_object* v_x_743_, lean_object* v_handle_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Option_tryCatch___redArg(v_x_743_, v_handle_744_);
lean_dec(v_x_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch(lean_object* v_00_u03b1_746_, lean_object* v_x_747_, lean_object* v_handle_748_){
_start:
{
if (lean_obj_tag(v_x_747_) == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_box(0);
v___x_750_ = lean_apply_1(v_handle_748_, v___x_749_);
return v___x_750_;
}
else
{
lean_dec_ref(v_handle_748_);
lean_inc_ref(v_x_747_);
return v_x_747_;
}
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___boxed(lean_object* v_00_u03b1_751_, lean_object* v_x_752_, lean_object* v_handle_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Option_tryCatch(v_00_u03b1_751_, v_x_752_, v_handle_753_);
lean_dec(v_x_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption___lam__0(lean_object* v_00_u03b1_755_, lean_object* v_x_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = lean_box(0);
return v___x_757_;
}
}
lean_object* runtime_initialize_Init_Control_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Option_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Control_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Option_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Option_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Option_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
