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
LEAN_EXPORT uint8_t l_Option_instDecidableEq___redArg(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_){
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
LEAN_EXPORT lean_object* l_Option_instDecidableEq___redArg___boxed(lean_object* v_inst_11_, lean_object* v_a_12_, lean_object* v_b_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Option_instDecidableEq___redArg(v_inst_11_, v_a_12_, v_b_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableEq(lean_object* v_00_u03b1_16_, lean_object* v_inst_17_, lean_object* v_a_18_, lean_object* v_b_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = l_Option_instDecidableEq___redArg(v_inst_17_, v_a_18_, v_b_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableEq___boxed(lean_object* v_00_u03b1_21_, lean_object* v_inst_22_, lean_object* v_a_23_, lean_object* v_b_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Option_instDecidableEq(v_00_u03b1_21_, v_inst_22_, v_a_23_, v_b_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint8_t l_Option_decidableEqNone___redArg(lean_object* v_o_27_){
_start:
{
if (lean_obj_tag(v_o_27_) == 0)
{
uint8_t v___x_28_; 
v___x_28_ = 1;
return v___x_28_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = 0;
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l_Option_decidableEqNone___redArg___boxed(lean_object* v_o_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_Option_decidableEqNone___redArg(v_o_30_);
lean_dec(v_o_30_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT uint8_t l_Option_decidableEqNone(lean_object* v_00_u03b1_33_, lean_object* v_o_34_){
_start:
{
uint8_t v___x_35_; 
v___x_35_ = l_Option_decidableEqNone___redArg(v_o_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Option_decidableEqNone___boxed(lean_object* v_00_u03b1_36_, lean_object* v_o_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_Option_decidableEqNone(v_00_u03b1_36_, v_o_37_);
lean_dec(v_o_37_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT uint8_t l_Option_decidableNoneEq___redArg(lean_object* v_o_40_){
_start:
{
if (lean_obj_tag(v_o_40_) == 0)
{
uint8_t v___x_41_; 
v___x_41_ = 1;
return v___x_41_;
}
else
{
uint8_t v___x_42_; 
v___x_42_ = 0;
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Option_decidableNoneEq___redArg___boxed(lean_object* v_o_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l_Option_decidableNoneEq___redArg(v_o_43_);
lean_dec(v_o_43_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
LEAN_EXPORT uint8_t l_Option_decidableNoneEq(lean_object* v_00_u03b1_46_, lean_object* v_o_47_){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = l_Option_decidableNoneEq___redArg(v_o_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Option_decidableNoneEq___boxed(lean_object* v_00_u03b1_49_, lean_object* v_o_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Option_decidableNoneEq(v_00_u03b1_49_, v_o_50_);
lean_dec(v_o_50_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT lean_object* l_Option_getM___redArg(lean_object* v_inst_53_, lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v_failure_55_; lean_object* v___x_56_; 
v_failure_55_ = lean_ctor_get(v_inst_53_, 1);
lean_inc(v_failure_55_);
lean_dec_ref(v_inst_53_);
v___x_56_ = lean_apply_1(v_failure_55_, lean_box(0));
return v___x_56_;
}
else
{
lean_object* v_toApplicative_57_; lean_object* v_toPure_58_; lean_object* v_val_59_; lean_object* v___x_60_; 
v_toApplicative_57_ = lean_ctor_get(v_inst_53_, 0);
lean_inc_ref(v_toApplicative_57_);
lean_dec_ref(v_inst_53_);
v_toPure_58_ = lean_ctor_get(v_toApplicative_57_, 1);
lean_inc(v_toPure_58_);
lean_dec_ref(v_toApplicative_57_);
v_val_59_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_val_59_);
lean_dec_ref_known(v_x_54_, 1);
v___x_60_ = lean_apply_2(v_toPure_58_, lean_box(0), v_val_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l_Option_getM(lean_object* v_m_61_, lean_object* v_00_u03b1_62_, lean_object* v_inst_63_, lean_object* v_x_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Option_getM___redArg(v_inst_63_, v_x_64_);
return v___x_65_;
}
}
LEAN_EXPORT uint8_t l_Option_isSome___redArg(lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = 1;
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Option_isSome___redArg___boxed(lean_object* v_x_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Option_isSome___redArg(v_x_69_);
lean_dec(v_x_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint8_t l_Option_isSome(lean_object* v_00_u03b1_72_, lean_object* v_x_73_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
uint8_t v___x_74_; 
v___x_74_ = 0;
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 1;
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l_Option_isSome___boxed(lean_object* v_00_u03b1_76_, lean_object* v_x_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Option_isSome(v_00_u03b1_76_, v_x_77_);
lean_dec(v_x_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Option_isNone___redArg(lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
uint8_t v___x_81_; 
v___x_81_ = 1;
return v___x_81_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Option_isNone___redArg___boxed(lean_object* v_x_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Option_isNone___redArg(v_x_83_);
lean_dec(v_x_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT uint8_t l_Option_isNone(lean_object* v_00_u03b1_86_, lean_object* v_x_87_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
uint8_t v___x_88_; 
v___x_88_ = 1;
return v___x_88_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* l_Option_isNone___boxed(lean_object* v_00_u03b1_90_, lean_object* v_x_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Option_isNone(v_00_u03b1_90_, v_x_91_);
lean_dec(v_x_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_Option_isEqSome___redArg(lean_object* v_inst_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
uint8_t v___x_97_; 
lean_dec(v_x_96_);
lean_dec_ref(v_inst_94_);
v___x_97_ = 0;
return v___x_97_;
}
else
{
lean_object* v_val_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_val_98_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_val_98_);
lean_dec_ref_known(v_x_95_, 1);
v___x_99_ = lean_apply_2(v_inst_94_, v_val_98_, v_x_96_);
v___x_100_ = lean_unbox(v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Option_isEqSome___redArg___boxed(lean_object* v_inst_101_, lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Option_isEqSome___redArg(v_inst_101_, v_x_102_, v_x_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t l_Option_isEqSome(lean_object* v_00_u03b1_106_, lean_object* v_inst_107_, lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
uint8_t v___x_110_; 
lean_dec(v_x_109_);
lean_dec_ref(v_inst_107_);
v___x_110_ = 0;
return v___x_110_;
}
else
{
lean_object* v_val_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_val_111_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_val_111_);
lean_dec_ref_known(v_x_108_, 1);
v___x_112_ = lean_apply_2(v_inst_107_, v_val_111_, v_x_109_);
v___x_113_ = lean_unbox(v___x_112_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Option_isEqSome___boxed(lean_object* v_00_u03b1_114_, lean_object* v_inst_115_, lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Option_isEqSome(v_00_u03b1_114_, v_inst_115_, v_x_116_, v_x_117_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l_Option_bind___redArg(lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
if (lean_obj_tag(v_x_120_) == 0)
{
lean_object* v___x_122_; 
lean_dec_ref(v_x_121_);
v___x_122_ = lean_box(0);
return v___x_122_;
}
else
{
lean_object* v_val_123_; lean_object* v___x_124_; 
v_val_123_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v_x_120_, 1);
v___x_124_ = lean_apply_1(v_x_121_, v_val_123_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Option_bind(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v___x_129_; 
lean_dec_ref(v_x_128_);
v___x_129_ = lean_box(0);
return v___x_129_;
}
else
{
lean_object* v_val_130_; lean_object* v___x_131_; 
v_val_130_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_val_130_);
lean_dec_ref_known(v_x_127_, 1);
v___x_131_ = lean_apply_1(v_x_128_, v_val_130_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Option_bindM___redArg(lean_object* v_inst_132_, lean_object* v_f_133_, lean_object* v_x_134_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_f_133_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_2(v_inst_132_, lean_box(0), v___x_135_);
return v___x_136_;
}
else
{
lean_object* v_val_137_; lean_object* v___x_138_; 
lean_dec(v_inst_132_);
v_val_137_ = lean_ctor_get(v_x_134_, 0);
lean_inc(v_val_137_);
lean_dec_ref_known(v_x_134_, 1);
v___x_138_ = lean_apply_1(v_f_133_, v_val_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Option_bindM(lean_object* v_m_139_, lean_object* v_00_u03b1_140_, lean_object* v_00_u03b2_141_, lean_object* v_inst_142_, lean_object* v_f_143_, lean_object* v_x_144_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec(v_f_143_);
v___x_145_ = lean_box(0);
v___x_146_ = lean_apply_2(v_inst_142_, lean_box(0), v___x_145_);
return v___x_146_;
}
else
{
lean_object* v_val_147_; lean_object* v___x_148_; 
lean_dec(v_inst_142_);
v_val_147_ = lean_ctor_get(v_x_144_, 0);
lean_inc(v_val_147_);
lean_dec_ref_known(v_x_144_, 1);
v___x_148_ = lean_apply_1(v_f_143_, v_val_147_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_Option_mapM___redArg___lam__0(lean_object* v_val_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_150_, 0, v_val_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Option_mapM___redArg(lean_object* v_inst_152_, lean_object* v_f_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v_toPure_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v_f_153_);
v_toPure_155_ = lean_ctor_get(v_inst_152_, 1);
lean_inc(v_toPure_155_);
lean_dec_ref(v_inst_152_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_apply_2(v_toPure_155_, lean_box(0), v___x_156_);
return v___x_157_;
}
else
{
lean_object* v_toFunctor_158_; lean_object* v_val_159_; lean_object* v_map_160_; lean_object* v___f_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_toFunctor_158_ = lean_ctor_get(v_inst_152_, 0);
lean_inc_ref(v_toFunctor_158_);
lean_dec_ref(v_inst_152_);
v_val_159_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_val_159_);
lean_dec_ref_known(v_x_154_, 1);
v_map_160_ = lean_ctor_get(v_toFunctor_158_, 0);
lean_inc(v_map_160_);
lean_dec_ref(v_toFunctor_158_);
v___f_161_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_162_ = lean_apply_1(v_f_153_, v_val_159_);
v___x_163_ = lean_apply_4(v_map_160_, lean_box(0), lean_box(0), v___f_161_, v___x_162_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Option_mapM(lean_object* v_m_164_, lean_object* v_00_u03b1_165_, lean_object* v_00_u03b2_166_, lean_object* v_inst_167_, lean_object* v_f_168_, lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v_toPure_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v_f_168_);
v_toPure_170_ = lean_ctor_get(v_inst_167_, 1);
lean_inc(v_toPure_170_);
lean_dec_ref(v_inst_167_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_apply_2(v_toPure_170_, lean_box(0), v___x_171_);
return v___x_172_;
}
else
{
lean_object* v_toFunctor_173_; lean_object* v_val_174_; lean_object* v_map_175_; lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_toFunctor_173_ = lean_ctor_get(v_inst_167_, 0);
lean_inc_ref(v_toFunctor_173_);
lean_dec_ref(v_inst_167_);
v_val_174_ = lean_ctor_get(v_x_169_, 0);
lean_inc(v_val_174_);
lean_dec_ref_known(v_x_169_, 1);
v_map_175_ = lean_ctor_get(v_toFunctor_173_, 0);
lean_inc(v_map_175_);
lean_dec_ref(v_toFunctor_173_);
v___f_176_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_177_ = lean_apply_1(v_f_168_, v_val_174_);
v___x_178_ = lean_apply_4(v_map_175_, lean_box(0), lean_box(0), v___f_176_, v___x_177_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l_Option_mapA___redArg(lean_object* v_inst_179_, lean_object* v_f_180_, lean_object* v_a_181_){
_start:
{
if (lean_obj_tag(v_a_181_) == 0)
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
v_val_186_ = lean_ctor_get(v_a_181_, 0);
lean_inc(v_val_186_);
lean_dec_ref_known(v_a_181_, 1);
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
LEAN_EXPORT lean_object* l_Option_mapA(lean_object* v_m_191_, lean_object* v_00_u03b1_192_, lean_object* v_00_u03b2_193_, lean_object* v_inst_194_, lean_object* v_f_195_, lean_object* v_a_196_){
_start:
{
if (lean_obj_tag(v_a_196_) == 0)
{
lean_object* v_toPure_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v_f_195_);
v_toPure_197_ = lean_ctor_get(v_inst_194_, 1);
lean_inc(v_toPure_197_);
lean_dec_ref(v_inst_194_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_apply_2(v_toPure_197_, lean_box(0), v___x_198_);
return v___x_199_;
}
else
{
lean_object* v_toFunctor_200_; lean_object* v_val_201_; lean_object* v_map_202_; lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_toFunctor_200_ = lean_ctor_get(v_inst_194_, 0);
lean_inc_ref(v_toFunctor_200_);
lean_dec_ref(v_inst_194_);
v_val_201_ = lean_ctor_get(v_a_196_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v_a_196_, 1);
v_map_202_ = lean_ctor_get(v_toFunctor_200_, 0);
lean_inc(v_map_202_);
lean_dec_ref(v_toFunctor_200_);
v___f_203_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_204_ = lean_apply_1(v_f_195_, v_val_201_);
v___x_205_ = lean_apply_4(v_map_202_, lean_box(0), lean_box(0), v___f_203_, v___x_204_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_Option_filterM___redArg___lam__0(lean_object* v_x_206_, uint8_t v_b_207_){
_start:
{
if (v_b_207_ == 0)
{
lean_object* v___x_208_; 
v___x_208_ = lean_box(0);
return v___x_208_;
}
else
{
lean_inc(v_x_206_);
return v_x_206_;
}
}
}
LEAN_EXPORT lean_object* l_Option_filterM___redArg___lam__0___boxed(lean_object* v_x_209_, lean_object* v_b_210_){
_start:
{
uint8_t v_b_boxed_211_; lean_object* v_res_212_; 
v_b_boxed_211_ = lean_unbox(v_b_210_);
v_res_212_ = l_Option_filterM___redArg___lam__0(v_x_209_, v_b_boxed_211_);
lean_dec(v_x_209_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Option_filterM___redArg(lean_object* v_inst_213_, lean_object* v_p_214_, lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v_toPure_216_; lean_object* v___x_217_; 
lean_dec(v_p_214_);
v_toPure_216_ = lean_ctor_get(v_inst_213_, 1);
lean_inc(v_toPure_216_);
lean_dec_ref(v_inst_213_);
v___x_217_ = lean_apply_2(v_toPure_216_, lean_box(0), v_x_215_);
return v___x_217_;
}
else
{
lean_object* v_toFunctor_218_; lean_object* v_val_219_; lean_object* v_map_220_; lean_object* v___f_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_toFunctor_218_ = lean_ctor_get(v_inst_213_, 0);
lean_inc_ref(v_toFunctor_218_);
lean_dec_ref(v_inst_213_);
v_val_219_ = lean_ctor_get(v_x_215_, 0);
lean_inc(v_val_219_);
v_map_220_ = lean_ctor_get(v_toFunctor_218_, 0);
lean_inc(v_map_220_);
lean_dec_ref(v_toFunctor_218_);
v___f_221_ = lean_alloc_closure((void*)(l_Option_filterM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_221_, 0, v_x_215_);
v___x_222_ = lean_apply_1(v_p_214_, v_val_219_);
v___x_223_ = lean_apply_4(v_map_220_, lean_box(0), lean_box(0), v___f_221_, v___x_222_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Option_filterM(lean_object* v_m_224_, lean_object* v_00_u03b1_225_, lean_object* v_inst_226_, lean_object* v_p_227_, lean_object* v_x_228_){
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
LEAN_EXPORT lean_object* l_Option_filter___redArg(lean_object* v_p_237_, lean_object* v_x_238_){
_start:
{
if (lean_obj_tag(v_x_238_) == 0)
{
lean_dec_ref(v_p_237_);
return v_x_238_;
}
else
{
lean_object* v_val_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_val_239_ = lean_ctor_get(v_x_238_, 0);
lean_inc(v_val_239_);
v___x_240_ = lean_apply_1(v_p_237_, v_val_239_);
v___x_241_ = lean_unbox(v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
lean_dec_ref_known(v_x_238_, 1);
v___x_242_ = lean_box(0);
return v___x_242_;
}
else
{
return v_x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_filter(lean_object* v_00_u03b1_243_, lean_object* v_p_244_, lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
lean_dec_ref(v_p_244_);
return v_x_245_;
}
else
{
lean_object* v_val_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_val_246_ = lean_ctor_get(v_x_245_, 0);
lean_inc(v_val_246_);
v___x_247_ = lean_apply_1(v_p_244_, v_val_246_);
v___x_248_ = lean_unbox(v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; 
lean_dec_ref_known(v_x_245_, 1);
v___x_249_ = lean_box(0);
return v___x_249_;
}
else
{
return v_x_245_;
}
}
}
}
LEAN_EXPORT uint8_t l_Option_all___redArg(lean_object* v_p_250_, lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
uint8_t v___x_252_; 
lean_dec_ref(v_p_250_);
v___x_252_ = 1;
return v___x_252_;
}
else
{
lean_object* v_val_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_val_253_ = lean_ctor_get(v_x_251_, 0);
lean_inc(v_val_253_);
lean_dec_ref_known(v_x_251_, 1);
v___x_254_ = lean_apply_1(v_p_250_, v_val_253_);
v___x_255_ = lean_unbox(v___x_254_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Option_all___redArg___boxed(lean_object* v_p_256_, lean_object* v_x_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Option_all___redArg(v_p_256_, v_x_257_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT uint8_t l_Option_all(lean_object* v_00_u03b1_260_, lean_object* v_p_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
uint8_t v___x_263_; 
lean_dec_ref(v_p_261_);
v___x_263_ = 1;
return v___x_263_;
}
else
{
lean_object* v_val_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_val_264_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_val_264_);
lean_dec_ref_known(v_x_262_, 1);
v___x_265_ = lean_apply_1(v_p_261_, v_val_264_);
v___x_266_ = lean_unbox(v___x_265_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Option_all___boxed(lean_object* v_00_u03b1_267_, lean_object* v_p_268_, lean_object* v_x_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Option_all(v_00_u03b1_267_, v_p_268_, v_x_269_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT uint8_t l_Option_any___redArg(lean_object* v_p_272_, lean_object* v_x_273_){
_start:
{
if (lean_obj_tag(v_x_273_) == 0)
{
uint8_t v___x_274_; 
lean_dec_ref(v_p_272_);
v___x_274_ = 0;
return v___x_274_;
}
else
{
lean_object* v_val_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v_val_275_ = lean_ctor_get(v_x_273_, 0);
lean_inc(v_val_275_);
lean_dec_ref_known(v_x_273_, 1);
v___x_276_ = lean_apply_1(v_p_272_, v_val_275_);
v___x_277_ = lean_unbox(v___x_276_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Option_any___redArg___boxed(lean_object* v_p_278_, lean_object* v_x_279_){
_start:
{
uint8_t v_res_280_; lean_object* v_r_281_; 
v_res_280_ = l_Option_any___redArg(v_p_278_, v_x_279_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT uint8_t l_Option_any(lean_object* v_00_u03b1_282_, lean_object* v_p_283_, lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
uint8_t v___x_285_; 
lean_dec_ref(v_p_283_);
v___x_285_ = 0;
return v___x_285_;
}
else
{
lean_object* v_val_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_val_286_ = lean_ctor_get(v_x_284_, 0);
lean_inc(v_val_286_);
lean_dec_ref_known(v_x_284_, 1);
v___x_287_ = lean_apply_1(v_p_283_, v_val_286_);
v___x_288_ = lean_unbox(v___x_287_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l_Option_any___boxed(lean_object* v_00_u03b1_289_, lean_object* v_p_290_, lean_object* v_x_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Option_any(v_00_u03b1_289_, v_p_290_, v_x_291_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg___lam__0(lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_box(0);
v___x_297_ = lean_apply_1(v_x_295_, v___x_296_);
return v___x_297_;
}
else
{
lean_dec_ref(v_x_295_);
lean_inc_ref(v_x_294_);
return v_x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg___lam__0___boxed(lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Option_instOrElse___redArg___lam__0(v_x_298_, v_x_299_);
lean_dec(v_x_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg(){
_start:
{
lean_object* v___f_303_; 
v___f_303_ = ((lean_object*)(l_Option_instOrElse___redArg___closed__0));
return v___f_303_;
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg___boxed(lean_object* v___dummy_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Option_instOrElse___redArg();
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse(lean_object* v_00_u03b1_306_){
_start:
{
lean_object* v___f_307_; 
v___f_307_ = ((lean_object*)(l_Option_instOrElse___redArg___closed__0));
return v___f_307_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableRelLt___redArg(lean_object* v_s_308_, lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
lean_dec_ref(v_s_308_);
if (lean_obj_tag(v_x_310_) == 0)
{
uint8_t v___x_311_; 
v___x_311_ = 0;
return v___x_311_;
}
else
{
uint8_t v___x_312_; 
lean_dec_ref_known(v_x_310_, 1);
v___x_312_ = 1;
return v___x_312_;
}
}
else
{
if (lean_obj_tag(v_x_310_) == 0)
{
uint8_t v___x_313_; 
lean_dec_ref_known(v_x_309_, 1);
lean_dec_ref(v_s_308_);
v___x_313_ = 0;
return v___x_313_;
}
else
{
lean_object* v_val_314_; lean_object* v_val_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v_val_314_ = lean_ctor_get(v_x_309_, 0);
lean_inc(v_val_314_);
lean_dec_ref_known(v_x_309_, 1);
v_val_315_ = lean_ctor_get(v_x_310_, 0);
lean_inc(v_val_315_);
lean_dec_ref_known(v_x_310_, 1);
v___x_316_ = lean_apply_2(v_s_308_, v_val_314_, v_val_315_);
v___x_317_ = lean_unbox(v___x_316_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___redArg___boxed(lean_object* v_s_318_, lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Option_instDecidableRelLt___redArg(v_s_318_, v_x_319_, v_x_320_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableRelLt(lean_object* v_00_u03b1_323_, lean_object* v_00_u03b2_324_, lean_object* v_r_325_, lean_object* v_s_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = l_Option_instDecidableRelLt___redArg(v_s_326_, v_x_327_, v_x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___boxed(lean_object* v_00_u03b1_330_, lean_object* v_00_u03b2_331_, lean_object* v_r_332_, lean_object* v_s_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
uint8_t v_res_336_; lean_object* v_r_337_; 
v_res_336_ = l_Option_instDecidableRelLt(v_00_u03b1_330_, v_00_u03b2_331_, v_r_332_, v_s_333_, v_x_334_, v_x_335_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableRelLe___redArg(lean_object* v_s_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_339_) == 0)
{
uint8_t v___x_341_; 
lean_dec(v_x_340_);
lean_dec_ref(v_s_338_);
v___x_341_ = 1;
return v___x_341_;
}
else
{
if (lean_obj_tag(v_x_340_) == 0)
{
uint8_t v___x_342_; 
lean_dec_ref_known(v_x_339_, 1);
lean_dec_ref(v_s_338_);
v___x_342_ = 0;
return v___x_342_;
}
else
{
lean_object* v_val_343_; lean_object* v_val_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_val_343_ = lean_ctor_get(v_x_339_, 0);
lean_inc(v_val_343_);
lean_dec_ref_known(v_x_339_, 1);
v_val_344_ = lean_ctor_get(v_x_340_, 0);
lean_inc(v_val_344_);
lean_dec_ref_known(v_x_340_, 1);
v___x_345_ = lean_apply_2(v_s_338_, v_val_343_, v_val_344_);
v___x_346_ = lean_unbox(v___x_345_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLe___redArg___boxed(lean_object* v_s_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
uint8_t v_res_350_; lean_object* v_r_351_; 
v_res_350_ = l_Option_instDecidableRelLe___redArg(v_s_347_, v_x_348_, v_x_349_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableRelLe(lean_object* v_00_u03b1_352_, lean_object* v_00_u03b2_353_, lean_object* v_r_354_, lean_object* v_s_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = l_Option_instDecidableRelLe___redArg(v_s_355_, v_x_356_, v_x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLe___boxed(lean_object* v_00_u03b1_359_, lean_object* v_00_u03b2_360_, lean_object* v_r_361_, lean_object* v_s_362_, lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Option_instDecidableRelLe(v_00_u03b1_359_, v_00_u03b2_360_, v_r_361_, v_s_362_, v_x_363_, v_x_364_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT lean_object* l_Option_merge___redArg(lean_object* v_fn_367_, lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
if (lean_obj_tag(v_x_368_) == 0)
{
lean_dec(v_fn_367_);
return v_x_369_;
}
else
{
if (lean_obj_tag(v_x_369_) == 0)
{
lean_dec(v_fn_367_);
return v_x_368_;
}
else
{
lean_object* v_val_370_; lean_object* v_val_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_379_; 
v_val_370_ = lean_ctor_get(v_x_368_, 0);
lean_inc(v_val_370_);
lean_dec_ref_known(v_x_368_, 1);
v_val_371_ = lean_ctor_get(v_x_369_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v_x_369_);
if (v_isSharedCheck_379_ == 0)
{
v___x_373_ = v_x_369_;
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_val_371_);
lean_dec(v_x_369_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = lean_apply_2(v_fn_367_, v_val_370_, v_val_371_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_375_);
v___x_377_ = v___x_373_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_merge(lean_object* v_00_u03b1_380_, lean_object* v_fn_381_, lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Option_merge___redArg(v_fn_381_, v_x_382_, v_x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Option_elim___redArg(lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
if (lean_obj_tag(v_x_385_) == 0)
{
lean_dec(v_x_387_);
lean_inc(v_x_386_);
return v_x_386_;
}
else
{
lean_object* v_val_388_; lean_object* v___x_389_; 
v_val_388_ = lean_ctor_get(v_x_385_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v_x_385_, 1);
v___x_389_ = lean_apply_1(v_x_387_, v_val_388_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elim___redArg___boxed(lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Option_elim___redArg(v_x_390_, v_x_391_, v_x_392_);
lean_dec(v_x_391_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Option_elim(lean_object* v_00_u03b1_394_, lean_object* v_00_u03b2_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_396_) == 0)
{
lean_dec(v_x_398_);
lean_inc(v_x_397_);
return v_x_397_;
}
else
{
lean_object* v_val_399_; lean_object* v___x_400_; 
v_val_399_ = lean_ctor_get(v_x_396_, 0);
lean_inc(v_val_399_);
lean_dec_ref_known(v_x_396_, 1);
v___x_400_ = lean_apply_1(v_x_398_, v_val_399_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elim___boxed(lean_object* v_00_u03b1_401_, lean_object* v_00_u03b2_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Option_elim(v_00_u03b1_401_, v_00_u03b2_402_, v_x_403_, v_x_404_, v_x_405_);
lean_dec(v_x_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Option_get___redArg(lean_object* v_x_407_){
_start:
{
lean_object* v_val_408_; 
v_val_408_ = lean_ctor_get(v_x_407_, 0);
lean_inc(v_val_408_);
return v_val_408_;
}
}
LEAN_EXPORT lean_object* l_Option_get___redArg___boxed(lean_object* v_x_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Option_get___redArg(v_x_409_);
lean_dec(v_x_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Option_get(lean_object* v_00_u03b1_411_, lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
lean_object* v_val_414_; 
v_val_414_ = lean_ctor_get(v_x_412_, 0);
lean_inc(v_val_414_);
return v_val_414_;
}
}
LEAN_EXPORT lean_object* l_Option_get___boxed(lean_object* v_00_u03b1_415_, lean_object* v_x_416_, lean_object* v_x_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Option_get(v_00_u03b1_415_, v_x_416_, v_x_417_);
lean_dec(v_x_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Option_guard___redArg(lean_object* v_p_419_, lean_object* v_a_420_){
_start:
{
lean_object* v___x_421_; uint8_t v___x_422_; 
lean_inc(v_a_420_);
v___x_421_ = lean_apply_1(v_p_419_, v_a_420_);
v___x_422_ = lean_unbox(v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
lean_dec(v_a_420_);
v___x_423_ = lean_box(0);
return v___x_423_;
}
else
{
lean_object* v___x_424_; 
v___x_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_424_, 0, v_a_420_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Option_guard(lean_object* v_00_u03b1_425_, lean_object* v_p_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_428_; uint8_t v___x_429_; 
lean_inc(v_a_427_);
v___x_428_ = lean_apply_1(v_p_426_, v_a_427_);
v___x_429_ = lean_unbox(v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
lean_dec(v_a_427_);
v___x_430_ = lean_box(0);
return v___x_430_;
}
else
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v_a_427_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toList___redArg(lean_object* v_x_432_){
_start:
{
if (lean_obj_tag(v_x_432_) == 0)
{
lean_object* v___x_433_; 
v___x_433_ = lean_box(0);
return v___x_433_;
}
else
{
lean_object* v_val_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_val_434_ = lean_ctor_get(v_x_432_, 0);
v___x_435_ = lean_box(0);
lean_inc(v_val_434_);
v___x_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_436_, 0, v_val_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toList___redArg___boxed(lean_object* v_x_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Option_toList___redArg(v_x_437_);
lean_dec(v_x_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Option_toList(lean_object* v_00_u03b1_439_, lean_object* v_x_440_){
_start:
{
if (lean_obj_tag(v_x_440_) == 0)
{
lean_object* v___x_441_; 
v___x_441_ = lean_box(0);
return v___x_441_;
}
else
{
lean_object* v_val_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_val_442_ = lean_ctor_get(v_x_440_, 0);
v___x_443_ = lean_box(0);
lean_inc(v_val_442_);
v___x_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_444_, 0, v_val_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toList___boxed(lean_object* v_00_u03b1_445_, lean_object* v_x_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Option_toList(v_00_u03b1_445_, v_x_446_);
lean_dec(v_x_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Option_toArray___redArg(lean_object* v_x_450_){
_start:
{
if (lean_obj_tag(v_x_450_) == 0)
{
lean_object* v___x_451_; 
v___x_451_ = ((lean_object*)(l_Option_toArray___redArg___closed__0));
return v___x_451_;
}
else
{
lean_object* v_val_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_val_452_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_val_452_);
lean_dec_ref_known(v_x_450_, 1);
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = lean_mk_empty_array_with_capacity(v___x_453_);
v___x_455_ = lean_array_push(v___x_454_, v_val_452_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toArray(lean_object* v_00_u03b1_456_, lean_object* v_x_457_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
lean_object* v___x_458_; 
v___x_458_ = ((lean_object*)(l_Option_toArray___redArg___closed__0));
return v___x_458_;
}
else
{
lean_object* v_val_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_val_459_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_val_459_);
lean_dec_ref_known(v_x_457_, 1);
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_mk_empty_array_with_capacity(v___x_460_);
v___x_462_ = lean_array_push(v___x_461_, v_val_459_);
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Option_join___redArg(lean_object* v_x_463_){
_start:
{
if (lean_obj_tag(v_x_463_) == 0)
{
lean_object* v___x_464_; 
v___x_464_ = lean_box(0);
return v___x_464_;
}
else
{
lean_object* v_val_465_; 
v_val_465_ = lean_ctor_get(v_x_463_, 0);
lean_inc(v_val_465_);
return v_val_465_;
}
}
}
LEAN_EXPORT lean_object* l_Option_join___redArg___boxed(lean_object* v_x_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Option_join___redArg(v_x_466_);
lean_dec(v_x_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Option_join(lean_object* v_00_u03b1_468_, lean_object* v_x_469_){
_start:
{
if (lean_obj_tag(v_x_469_) == 0)
{
lean_object* v___x_470_; 
v___x_470_ = lean_box(0);
return v___x_470_;
}
else
{
lean_object* v_val_471_; 
v_val_471_ = lean_ctor_get(v_x_469_, 0);
lean_inc(v_val_471_);
return v_val_471_;
}
}
}
LEAN_EXPORT lean_object* l_Option_join___boxed(lean_object* v_00_u03b1_472_, lean_object* v_x_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Option_join(v_00_u03b1_472_, v_x_473_);
lean_dec(v_x_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Option_sequence___redArg(lean_object* v_inst_475_, lean_object* v_x_476_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_object* v_toPure_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_toPure_477_ = lean_ctor_get(v_inst_475_, 1);
lean_inc(v_toPure_477_);
lean_dec_ref(v_inst_475_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_apply_2(v_toPure_477_, lean_box(0), v___x_478_);
return v___x_479_;
}
else
{
lean_object* v_toFunctor_480_; lean_object* v_val_481_; lean_object* v_map_482_; lean_object* v___f_483_; lean_object* v___x_484_; 
v_toFunctor_480_ = lean_ctor_get(v_inst_475_, 0);
lean_inc_ref(v_toFunctor_480_);
lean_dec_ref(v_inst_475_);
v_val_481_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_val_481_);
lean_dec_ref_known(v_x_476_, 1);
v_map_482_ = lean_ctor_get(v_toFunctor_480_, 0);
lean_inc(v_map_482_);
lean_dec_ref(v_toFunctor_480_);
v___f_483_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_484_ = lean_apply_4(v_map_482_, lean_box(0), lean_box(0), v___f_483_, v_val_481_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l_Option_sequence(lean_object* v_m_485_, lean_object* v_inst_486_, lean_object* v_00_u03b1_487_, lean_object* v_x_488_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
lean_object* v_toPure_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_toPure_489_ = lean_ctor_get(v_inst_486_, 1);
lean_inc(v_toPure_489_);
lean_dec_ref(v_inst_486_);
v___x_490_ = lean_box(0);
v___x_491_ = lean_apply_2(v_toPure_489_, lean_box(0), v___x_490_);
return v___x_491_;
}
else
{
lean_object* v_toFunctor_492_; lean_object* v_val_493_; lean_object* v_map_494_; lean_object* v___f_495_; lean_object* v___x_496_; 
v_toFunctor_492_ = lean_ctor_get(v_inst_486_, 0);
lean_inc_ref(v_toFunctor_492_);
lean_dec_ref(v_inst_486_);
v_val_493_ = lean_ctor_get(v_x_488_, 0);
lean_inc(v_val_493_);
lean_dec_ref_known(v_x_488_, 1);
v_map_494_ = lean_ctor_get(v_toFunctor_492_, 0);
lean_inc(v_map_494_);
lean_dec_ref(v_toFunctor_492_);
v___f_495_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_496_ = lean_apply_4(v_map_494_, lean_box(0), lean_box(0), v___f_495_, v_val_493_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elimM___redArg___lam__0(lean_object* v_y_497_, lean_object* v_z_498_, lean_object* v_____do__lift_499_){
_start:
{
if (lean_obj_tag(v_____do__lift_499_) == 0)
{
lean_dec(v_z_498_);
lean_inc(v_y_497_);
return v_y_497_;
}
else
{
lean_object* v_val_500_; lean_object* v___x_501_; 
v_val_500_ = lean_ctor_get(v_____do__lift_499_, 0);
lean_inc(v_val_500_);
lean_dec_ref_known(v_____do__lift_499_, 1);
v___x_501_ = lean_apply_1(v_z_498_, v_val_500_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elimM___redArg___lam__0___boxed(lean_object* v_y_502_, lean_object* v_z_503_, lean_object* v_____do__lift_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Option_elimM___redArg___lam__0(v_y_502_, v_z_503_, v_____do__lift_504_);
lean_dec(v_y_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Option_elimM___redArg(lean_object* v_inst_506_, lean_object* v_x_507_, lean_object* v_y_508_, lean_object* v_z_509_){
_start:
{
lean_object* v_toBind_510_; lean_object* v___f_511_; lean_object* v___x_512_; 
v_toBind_510_ = lean_ctor_get(v_inst_506_, 1);
lean_inc(v_toBind_510_);
lean_dec_ref(v_inst_506_);
v___f_511_ = lean_alloc_closure((void*)(l_Option_elimM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_511_, 0, v_y_508_);
lean_closure_set(v___f_511_, 1, v_z_509_);
v___x_512_ = lean_apply_4(v_toBind_510_, lean_box(0), lean_box(0), v_x_507_, v___f_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Option_elimM(lean_object* v_m_513_, lean_object* v_00_u03b1_514_, lean_object* v_00_u03b2_515_, lean_object* v_inst_516_, lean_object* v_x_517_, lean_object* v_y_518_, lean_object* v_z_519_){
_start:
{
lean_object* v_toBind_520_; lean_object* v___f_521_; lean_object* v___x_522_; 
v_toBind_520_ = lean_ctor_get(v_inst_516_, 1);
lean_inc(v_toBind_520_);
lean_dec_ref(v_inst_516_);
v___f_521_ = lean_alloc_closure((void*)(l_Option_elimM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_521_, 0, v_y_518_);
lean_closure_set(v___f_521_, 1, v_z_519_);
v___x_522_ = lean_apply_4(v_toBind_520_, lean_box(0), lean_box(0), v_x_517_, v___f_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Option_getDM___redArg(lean_object* v_inst_523_, lean_object* v_x_524_, lean_object* v_y_525_){
_start:
{
if (lean_obj_tag(v_x_524_) == 0)
{
lean_dec(v_inst_523_);
lean_inc(v_y_525_);
return v_y_525_;
}
else
{
lean_object* v_val_526_; lean_object* v___x_527_; 
v_val_526_ = lean_ctor_get(v_x_524_, 0);
lean_inc(v_val_526_);
lean_dec_ref_known(v_x_524_, 1);
v___x_527_ = lean_apply_2(v_inst_523_, lean_box(0), v_val_526_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l_Option_getDM___redArg___boxed(lean_object* v_inst_528_, lean_object* v_x_529_, lean_object* v_y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Option_getDM___redArg(v_inst_528_, v_x_529_, v_y_530_);
lean_dec(v_y_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Option_getDM(lean_object* v_m_532_, lean_object* v_00_u03b1_533_, lean_object* v_inst_534_, lean_object* v_x_535_, lean_object* v_y_536_){
_start:
{
if (lean_obj_tag(v_x_535_) == 0)
{
lean_dec(v_inst_534_);
lean_inc(v_y_536_);
return v_y_536_;
}
else
{
lean_object* v_val_537_; lean_object* v___x_538_; 
v_val_537_ = lean_ctor_get(v_x_535_, 0);
lean_inc(v_val_537_);
lean_dec_ref_known(v_x_535_, 1);
v___x_538_ = lean_apply_2(v_inst_534_, lean_box(0), v_val_537_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_Option_getDM___boxed(lean_object* v_m_539_, lean_object* v_00_u03b1_540_, lean_object* v_inst_541_, lean_object* v_x_542_, lean_object* v_y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Option_getDM(v_m_539_, v_00_u03b1_540_, v_inst_541_, v_x_542_, v_y_543_);
lean_dec(v_y_543_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Option_min___redArg(lean_object* v_inst_545_, lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
if (lean_obj_tag(v_x_546_) == 0)
{
lean_dec(v_inst_545_);
if (lean_obj_tag(v_x_547_) == 0)
{
return v_x_547_;
}
else
{
lean_dec_ref_known(v_x_547_, 1);
return v_x_546_;
}
}
else
{
if (lean_obj_tag(v_x_547_) == 0)
{
lean_dec_ref_known(v_x_546_, 1);
lean_dec(v_inst_545_);
return v_x_547_;
}
else
{
lean_object* v_val_548_; lean_object* v_val_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_557_; 
v_val_548_ = lean_ctor_get(v_x_546_, 0);
lean_inc(v_val_548_);
lean_dec_ref_known(v_x_546_, 1);
v_val_549_ = lean_ctor_get(v_x_547_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v_x_547_);
if (v_isSharedCheck_557_ == 0)
{
v___x_551_ = v_x_547_;
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_val_549_);
lean_dec(v_x_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_apply_2(v_inst_545_, v_val_548_, v_val_549_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_min(lean_object* v_00_u03b1_558_, lean_object* v_inst_559_, lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Option_min___redArg(v_inst_559_, v_x_560_, v_x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Option_instMin___redArg(lean_object* v_inst_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = lean_alloc_closure((void*)(l_Option_min), 4, 2);
lean_closure_set(v___x_564_, 0, lean_box(0));
lean_closure_set(v___x_564_, 1, v_inst_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Option_instMin(lean_object* v_00_u03b1_565_, lean_object* v_inst_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_alloc_closure((void*)(l_Option_min), 4, 2);
lean_closure_set(v___x_567_, 0, lean_box(0));
lean_closure_set(v___x_567_, 1, v_inst_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Option_max___redArg(lean_object* v_inst_568_, lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
if (lean_obj_tag(v_x_569_) == 0)
{
lean_dec(v_inst_568_);
return v_x_570_;
}
else
{
if (lean_obj_tag(v_x_570_) == 0)
{
lean_dec(v_inst_568_);
return v_x_569_;
}
else
{
lean_object* v_val_571_; lean_object* v_val_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_580_; 
v_val_571_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_val_571_);
lean_dec_ref_known(v_x_569_, 1);
v_val_572_ = lean_ctor_get(v_x_570_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v_x_570_);
if (v_isSharedCheck_580_ == 0)
{
v___x_574_ = v_x_570_;
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_val_572_);
lean_dec(v_x_570_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_576_ = lean_apply_2(v_inst_568_, v_val_571_, v_val_572_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_576_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_max(lean_object* v_00_u03b1_581_, lean_object* v_inst_582_, lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Option_max___redArg(v_inst_582_, v_x_583_, v_x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Option_instMax___redArg(lean_object* v_inst_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_closure((void*)(l_Option_max), 4, 2);
lean_closure_set(v___x_587_, 0, lean_box(0));
lean_closure_set(v___x_587_, 1, v_inst_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Option_instMax(lean_object* v_00_u03b1_588_, lean_object* v_inst_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = lean_alloc_closure((void*)(l_Option_max), 4, 2);
lean_closure_set(v___x_590_, 0, lean_box(0));
lean_closure_set(v___x_590_, 1, v_inst_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_instLTOption___redArg(){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = lean_box(0);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_instLTOption___redArg___boxed(lean_object* v___dummy_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_instLTOption___redArg();
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_instLTOption(lean_object* v_00_u03b1_595_, lean_object* v_inst_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = lean_box(0);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_instLEOption___redArg(){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_box(0);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_instLEOption___redArg___boxed(lean_object* v___dummy_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_instLEOption___redArg();
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_instLEOption(lean_object* v_00_u03b1_602_, lean_object* v_inst_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = lean_box(0);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_instFunctorOption___lam__0(lean_object* v_00_u03b1_605_, lean_object* v_00_u03b2_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
if (lean_obj_tag(v___y_608_) == 0)
{
lean_object* v___x_609_; 
lean_dec(v___y_607_);
v___x_609_ = lean_box(0);
return v___x_609_;
}
else
{
lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_isSharedCheck_616_ = !lean_is_exclusive(v___y_608_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v___y_608_, 0);
lean_dec(v_unused_617_);
v___x_611_ = v___y_608_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_dec(v___y_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___y_607_);
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___y_607_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__0(lean_object* v_00_u03b1_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___y_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__1(lean_object* v_00_u03b1_627_, lean_object* v_00_u03b2_628_, lean_object* v_f_629_, lean_object* v_x_630_){
_start:
{
if (lean_obj_tag(v_f_629_) == 0)
{
lean_object* v___x_631_; 
lean_dec_ref(v_x_630_);
v___x_631_ = lean_box(0);
return v___x_631_;
}
else
{
lean_object* v_val_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_val_632_ = lean_ctor_get(v_f_629_, 0);
lean_inc(v_val_632_);
lean_dec_ref_known(v_f_629_, 1);
v___x_633_ = lean_box(0);
v___x_634_ = lean_apply_1(v_x_630_, v___x_633_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v___x_635_; 
lean_dec(v_val_632_);
v___x_635_ = lean_box(0);
return v___x_635_;
}
else
{
lean_object* v_val_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_644_; 
v_val_636_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_644_ == 0)
{
v___x_638_ = v___x_634_;
v_isShared_639_ = v_isSharedCheck_644_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_val_636_);
lean_dec(v___x_634_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_644_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_640_ = lean_apply_1(v_val_632_, v_val_636_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_640_);
v___x_642_ = v___x_638_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__2(lean_object* v_00_u03b1_645_, lean_object* v_00_u03b2_646_, lean_object* v_x_647_, lean_object* v_y_648_){
_start:
{
if (lean_obj_tag(v_x_647_) == 0)
{
lean_dec_ref(v_y_648_);
return v_x_647_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_box(0);
v___x_650_ = lean_apply_1(v_y_648_, v___x_649_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_651_; 
v___x_651_ = lean_box(0);
return v___x_651_;
}
else
{
lean_dec_ref_known(v___x_650_, 1);
lean_inc_ref(v_x_647_);
return v_x_647_;
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__2___boxed(lean_object* v_00_u03b1_652_, lean_object* v_00_u03b2_653_, lean_object* v_x_654_, lean_object* v_y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_instMonadOption___lam__2(v_00_u03b1_652_, v_00_u03b2_653_, v_x_654_, v_y_655_);
lean_dec(v_x_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__3(lean_object* v_00_u03b1_657_, lean_object* v_00_u03b2_658_, lean_object* v_x_659_, lean_object* v_y_660_){
_start:
{
if (lean_obj_tag(v_x_659_) == 0)
{
lean_object* v___x_661_; 
lean_dec_ref(v_y_660_);
v___x_661_ = lean_box(0);
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_box(0);
v___x_663_ = lean_apply_1(v_y_660_, v___x_662_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__3___boxed(lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_x_666_, lean_object* v_y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_instMonadOption___lam__3(v_00_u03b1_664_, v_00_u03b2_665_, v_x_666_, v_y_667_);
lean_dec(v_x_666_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__0(lean_object* v_00_u03b1_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = lean_box(0);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__1(lean_object* v_00_u03b1_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
if (lean_obj_tag(v_x_687_) == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_box(0);
v___x_690_ = lean_apply_1(v_x_688_, v___x_689_);
return v___x_690_;
}
else
{
lean_dec_ref(v_x_688_);
lean_inc_ref(v_x_687_);
return v_x_687_;
}
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__1___boxed(lean_object* v_00_u03b1_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_instAlternativeOption___lam__1(v_00_u03b1_691_, v_x_692_, v_x_693_);
lean_dec(v_x_692_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_liftOption___redArg(lean_object* v_inst_702_, lean_object* v_x_703_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
lean_object* v_failure_704_; lean_object* v___x_705_; 
v_failure_704_ = lean_ctor_get(v_inst_702_, 1);
lean_inc(v_failure_704_);
lean_dec_ref(v_inst_702_);
v___x_705_ = lean_apply_1(v_failure_704_, lean_box(0));
return v___x_705_;
}
else
{
lean_object* v_toApplicative_706_; lean_object* v_toPure_707_; lean_object* v_val_708_; lean_object* v___x_709_; 
v_toApplicative_706_ = lean_ctor_get(v_inst_702_, 0);
lean_inc_ref(v_toApplicative_706_);
lean_dec_ref(v_inst_702_);
v_toPure_707_ = lean_ctor_get(v_toApplicative_706_, 1);
lean_inc(v_toPure_707_);
lean_dec_ref(v_toApplicative_706_);
v_val_708_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v_x_703_, 1);
v___x_709_ = lean_apply_2(v_toPure_707_, lean_box(0), v_val_708_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_liftOption(lean_object* v_m_710_, lean_object* v_00_u03b1_711_, lean_object* v_inst_712_, lean_object* v_x_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_liftOption___redArg(v_inst_712_, v_x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___redArg(lean_object* v_x_715_, lean_object* v_handle_716_){
_start:
{
if (lean_obj_tag(v_x_715_) == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_box(0);
v___x_718_ = lean_apply_1(v_handle_716_, v___x_717_);
return v___x_718_;
}
else
{
lean_dec_ref(v_handle_716_);
lean_inc_ref(v_x_715_);
return v_x_715_;
}
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___redArg___boxed(lean_object* v_x_719_, lean_object* v_handle_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Option_tryCatch___redArg(v_x_719_, v_handle_720_);
lean_dec(v_x_719_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch(lean_object* v_00_u03b1_722_, lean_object* v_x_723_, lean_object* v_handle_724_){
_start:
{
if (lean_obj_tag(v_x_723_) == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_box(0);
v___x_726_ = lean_apply_1(v_handle_724_, v___x_725_);
return v___x_726_;
}
else
{
lean_dec_ref(v_handle_724_);
lean_inc_ref(v_x_723_);
return v_x_723_;
}
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___boxed(lean_object* v_00_u03b1_727_, lean_object* v_x_728_, lean_object* v_handle_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Option_tryCatch(v_00_u03b1_727_, v_x_728_, v_handle_729_);
lean_dec(v_x_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption___lam__0(lean_object* v_00_u03b1_731_, lean_object* v_x_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_box(0);
return v___x_733_;
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
