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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Option_instOrElse___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instOrElse___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Option_instOrElse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_instOrElse___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Option_instOrElse___closed__0 = (const lean_object*)&l_Option_instOrElse___closed__0_value;
LEAN_EXPORT lean_object* l_Option_instOrElse(lean_object*);
LEAN_EXPORT uint8_t l_Option_instDecidableRelLt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instDecidableRelLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_instLTOption(lean_object*, lean_object*);
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
lean_dec_ref(v_b_3_);
v___x_5_ = 0;
return v___x_5_;
}
}
else
{
if (lean_obj_tag(v_b_3_) == 0)
{
uint8_t v___x_6_; 
lean_dec_ref(v_a_2_);
lean_dec_ref(v_inst_1_);
v___x_6_ = 0;
return v___x_6_;
}
else
{
lean_object* v_val_7_; lean_object* v_val_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_val_7_ = lean_ctor_get(v_a_2_, 0);
lean_inc(v_val_7_);
lean_dec_ref(v_a_2_);
v_val_8_ = lean_ctor_get(v_b_3_, 0);
lean_inc(v_val_8_);
lean_dec_ref(v_b_3_);
v___x_9_ = lean_apply_2(v_inst_1_, v_val_7_, v_val_8_);
v___x_10_ = lean_unbox(v___x_9_);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___redArg(lean_object* v_inst_53_, lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_dec_ref(v_inst_53_);
if (lean_obj_tag(v_x_55_) == 0)
{
uint8_t v___x_56_; 
v___x_56_ = 1;
return v___x_56_;
}
else
{
uint8_t v___x_57_; 
lean_dec_ref(v_x_55_);
v___x_57_ = 0;
return v___x_57_;
}
}
else
{
if (lean_obj_tag(v_x_55_) == 0)
{
uint8_t v___x_58_; 
lean_dec_ref(v_x_54_);
lean_dec_ref(v_inst_53_);
v___x_58_ = 0;
return v___x_58_;
}
else
{
lean_object* v_val_59_; lean_object* v_val_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_val_59_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_val_59_);
lean_dec_ref(v_x_54_);
v_val_60_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_val_60_);
lean_dec_ref(v_x_55_);
v___x_61_ = lean_apply_2(v_inst_53_, v_val_59_, v_val_60_);
v___x_62_ = lean_unbox(v___x_61_);
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___redArg___boxed(lean_object* v_inst_63_, lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Option_instBEq_beq___redArg(v_inst_63_, v_x_64_, v_x_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq(lean_object* v_00_u03b1_68_, lean_object* v_inst_69_, lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
uint8_t v___x_72_; 
v___x_72_ = l_Option_instBEq_beq___redArg(v_inst_69_, v_x_70_, v_x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___boxed(lean_object* v_00_u03b1_73_, lean_object* v_inst_74_, lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Option_instBEq_beq(v_00_u03b1_73_, v_inst_74_, v_x_75_, v_x_76_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* l_Option_instBEq___redArg(lean_object* v_inst_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_alloc_closure((void*)(l_Option_instBEq_beq___boxed), 4, 2);
lean_closure_set(v___x_80_, 0, lean_box(0));
lean_closure_set(v___x_80_, 1, v_inst_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Option_instBEq(lean_object* v_00_u03b1_81_, lean_object* v_inst_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_closure((void*)(l_Option_instBEq_beq___boxed), 4, 2);
lean_closure_set(v___x_83_, 0, lean_box(0));
lean_closure_set(v___x_83_, 1, v_inst_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Option_getM___redArg(lean_object* v_inst_84_, lean_object* v_x_85_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v_failure_86_; lean_object* v___x_87_; 
v_failure_86_ = lean_ctor_get(v_inst_84_, 1);
lean_inc(v_failure_86_);
lean_dec_ref(v_inst_84_);
v___x_87_ = lean_apply_1(v_failure_86_, lean_box(0));
return v___x_87_;
}
else
{
lean_object* v_toApplicative_88_; lean_object* v_toPure_89_; lean_object* v_val_90_; lean_object* v___x_91_; 
v_toApplicative_88_ = lean_ctor_get(v_inst_84_, 0);
lean_inc_ref(v_toApplicative_88_);
lean_dec_ref(v_inst_84_);
v_toPure_89_ = lean_ctor_get(v_toApplicative_88_, 1);
lean_inc(v_toPure_89_);
lean_dec_ref(v_toApplicative_88_);
v_val_90_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_val_90_);
lean_dec_ref(v_x_85_);
v___x_91_ = lean_apply_2(v_toPure_89_, lean_box(0), v_val_90_);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l_Option_getM(lean_object* v_m_92_, lean_object* v_00_u03b1_93_, lean_object* v_inst_94_, lean_object* v_x_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Option_getM___redArg(v_inst_94_, v_x_95_);
return v___x_96_;
}
}
LEAN_EXPORT uint8_t l_Option_isSome___redArg(lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_97_) == 0)
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
else
{
uint8_t v___x_99_; 
v___x_99_ = 1;
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Option_isSome___redArg___boxed(lean_object* v_x_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Option_isSome___redArg(v_x_100_);
lean_dec(v_x_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT uint8_t l_Option_isSome(lean_object* v_00_u03b1_103_, lean_object* v_x_104_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = 1;
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Option_isSome___boxed(lean_object* v_00_u03b1_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Option_isSome(v_00_u03b1_107_, v_x_108_);
lean_dec(v_x_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_Option_isNone___redArg(lean_object* v_x_111_){
_start:
{
if (lean_obj_tag(v_x_111_) == 0)
{
uint8_t v___x_112_; 
v___x_112_ = 1;
return v___x_112_;
}
else
{
uint8_t v___x_113_; 
v___x_113_ = 0;
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Option_isNone___redArg___boxed(lean_object* v_x_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Option_isNone___redArg(v_x_114_);
lean_dec(v_x_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT uint8_t l_Option_isNone(lean_object* v_00_u03b1_117_, lean_object* v_x_118_){
_start:
{
if (lean_obj_tag(v_x_118_) == 0)
{
uint8_t v___x_119_; 
v___x_119_ = 1;
return v___x_119_;
}
else
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l_Option_isNone___boxed(lean_object* v_00_u03b1_121_, lean_object* v_x_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Option_isNone(v_00_u03b1_121_, v_x_122_);
lean_dec(v_x_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT uint8_t l_Option_isEqSome___redArg(lean_object* v_inst_125_, lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
uint8_t v___x_128_; 
lean_dec(v_x_127_);
lean_dec_ref(v_inst_125_);
v___x_128_ = 0;
return v___x_128_;
}
else
{
lean_object* v_val_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v_val_129_ = lean_ctor_get(v_x_126_, 0);
lean_inc(v_val_129_);
lean_dec_ref(v_x_126_);
v___x_130_ = lean_apply_2(v_inst_125_, v_val_129_, v_x_127_);
v___x_131_ = lean_unbox(v___x_130_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Option_isEqSome___redArg___boxed(lean_object* v_inst_132_, lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Option_isEqSome___redArg(v_inst_132_, v_x_133_, v_x_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT uint8_t l_Option_isEqSome(lean_object* v_00_u03b1_137_, lean_object* v_inst_138_, lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
uint8_t v___x_141_; 
lean_dec(v_x_140_);
lean_dec_ref(v_inst_138_);
v___x_141_ = 0;
return v___x_141_;
}
else
{
lean_object* v_val_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_val_142_ = lean_ctor_get(v_x_139_, 0);
lean_inc(v_val_142_);
lean_dec_ref(v_x_139_);
v___x_143_ = lean_apply_2(v_inst_138_, v_val_142_, v_x_140_);
v___x_144_ = lean_unbox(v___x_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Option_isEqSome___boxed(lean_object* v_00_u03b1_145_, lean_object* v_inst_146_, lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Option_isEqSome(v_00_u03b1_145_, v_inst_146_, v_x_147_, v_x_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_Option_bind___redArg(lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_151_) == 0)
{
lean_object* v___x_153_; 
lean_dec_ref(v_x_152_);
v___x_153_ = lean_box(0);
return v___x_153_;
}
else
{
lean_object* v_val_154_; lean_object* v___x_155_; 
v_val_154_ = lean_ctor_get(v_x_151_, 0);
lean_inc(v_val_154_);
lean_dec_ref(v_x_151_);
v___x_155_ = lean_apply_1(v_x_152_, v_val_154_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Option_bind(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v___x_160_; 
lean_dec_ref(v_x_159_);
v___x_160_ = lean_box(0);
return v___x_160_;
}
else
{
lean_object* v_val_161_; lean_object* v___x_162_; 
v_val_161_ = lean_ctor_get(v_x_158_, 0);
lean_inc(v_val_161_);
lean_dec_ref(v_x_158_);
v___x_162_ = lean_apply_1(v_x_159_, v_val_161_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Option_bindM___redArg(lean_object* v_inst_163_, lean_object* v_f_164_, lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_f_164_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_2(v_inst_163_, lean_box(0), v___x_166_);
return v___x_167_;
}
else
{
lean_object* v_val_168_; lean_object* v___x_169_; 
lean_dec(v_inst_163_);
v_val_168_ = lean_ctor_get(v_x_165_, 0);
lean_inc(v_val_168_);
lean_dec_ref(v_x_165_);
v___x_169_ = lean_apply_1(v_f_164_, v_val_168_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Option_bindM(lean_object* v_m_170_, lean_object* v_00_u03b1_171_, lean_object* v_00_u03b2_172_, lean_object* v_inst_173_, lean_object* v_f_174_, lean_object* v_x_175_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v_f_174_);
v___x_176_ = lean_box(0);
v___x_177_ = lean_apply_2(v_inst_173_, lean_box(0), v___x_176_);
return v___x_177_;
}
else
{
lean_object* v_val_178_; lean_object* v___x_179_; 
lean_dec(v_inst_173_);
v_val_178_ = lean_ctor_get(v_x_175_, 0);
lean_inc(v_val_178_);
lean_dec_ref(v_x_175_);
v___x_179_ = lean_apply_1(v_f_174_, v_val_178_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l_Option_mapM___redArg___lam__0(lean_object* v_val_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_val_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Option_mapM___redArg(lean_object* v_inst_183_, lean_object* v_f_184_, lean_object* v_x_185_){
_start:
{
if (lean_obj_tag(v_x_185_) == 0)
{
lean_object* v_toPure_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v_f_184_);
v_toPure_186_ = lean_ctor_get(v_inst_183_, 1);
lean_inc(v_toPure_186_);
lean_dec_ref(v_inst_183_);
v___x_187_ = lean_box(0);
v___x_188_ = lean_apply_2(v_toPure_186_, lean_box(0), v___x_187_);
return v___x_188_;
}
else
{
lean_object* v_toFunctor_189_; lean_object* v_val_190_; lean_object* v_map_191_; lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_toFunctor_189_ = lean_ctor_get(v_inst_183_, 0);
lean_inc_ref(v_toFunctor_189_);
lean_dec_ref(v_inst_183_);
v_val_190_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_val_190_);
lean_dec_ref(v_x_185_);
v_map_191_ = lean_ctor_get(v_toFunctor_189_, 0);
lean_inc(v_map_191_);
lean_dec_ref(v_toFunctor_189_);
v___f_192_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_193_ = lean_apply_1(v_f_184_, v_val_190_);
v___x_194_ = lean_apply_4(v_map_191_, lean_box(0), lean_box(0), v___f_192_, v___x_193_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Option_mapM(lean_object* v_m_195_, lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_inst_198_, lean_object* v_f_199_, lean_object* v_x_200_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
lean_object* v_toPure_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_f_199_);
v_toPure_201_ = lean_ctor_get(v_inst_198_, 1);
lean_inc(v_toPure_201_);
lean_dec_ref(v_inst_198_);
v___x_202_ = lean_box(0);
v___x_203_ = lean_apply_2(v_toPure_201_, lean_box(0), v___x_202_);
return v___x_203_;
}
else
{
lean_object* v_toFunctor_204_; lean_object* v_val_205_; lean_object* v_map_206_; lean_object* v___f_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_toFunctor_204_ = lean_ctor_get(v_inst_198_, 0);
lean_inc_ref(v_toFunctor_204_);
lean_dec_ref(v_inst_198_);
v_val_205_ = lean_ctor_get(v_x_200_, 0);
lean_inc(v_val_205_);
lean_dec_ref(v_x_200_);
v_map_206_ = lean_ctor_get(v_toFunctor_204_, 0);
lean_inc(v_map_206_);
lean_dec_ref(v_toFunctor_204_);
v___f_207_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_208_ = lean_apply_1(v_f_199_, v_val_205_);
v___x_209_ = lean_apply_4(v_map_206_, lean_box(0), lean_box(0), v___f_207_, v___x_208_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l_Option_mapA___redArg(lean_object* v_inst_210_, lean_object* v_f_211_, lean_object* v_a_212_){
_start:
{
if (lean_obj_tag(v_a_212_) == 0)
{
lean_object* v_toPure_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v_f_211_);
v_toPure_213_ = lean_ctor_get(v_inst_210_, 1);
lean_inc(v_toPure_213_);
lean_dec_ref(v_inst_210_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_apply_2(v_toPure_213_, lean_box(0), v___x_214_);
return v___x_215_;
}
else
{
lean_object* v_toFunctor_216_; lean_object* v_val_217_; lean_object* v_map_218_; lean_object* v___f_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_toFunctor_216_ = lean_ctor_get(v_inst_210_, 0);
lean_inc_ref(v_toFunctor_216_);
lean_dec_ref(v_inst_210_);
v_val_217_ = lean_ctor_get(v_a_212_, 0);
lean_inc(v_val_217_);
lean_dec_ref(v_a_212_);
v_map_218_ = lean_ctor_get(v_toFunctor_216_, 0);
lean_inc(v_map_218_);
lean_dec_ref(v_toFunctor_216_);
v___f_219_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_220_ = lean_apply_1(v_f_211_, v_val_217_);
v___x_221_ = lean_apply_4(v_map_218_, lean_box(0), lean_box(0), v___f_219_, v___x_220_);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l_Option_mapA(lean_object* v_m_222_, lean_object* v_00_u03b1_223_, lean_object* v_00_u03b2_224_, lean_object* v_inst_225_, lean_object* v_f_226_, lean_object* v_a_227_){
_start:
{
if (lean_obj_tag(v_a_227_) == 0)
{
lean_object* v_toPure_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec(v_f_226_);
v_toPure_228_ = lean_ctor_get(v_inst_225_, 1);
lean_inc(v_toPure_228_);
lean_dec_ref(v_inst_225_);
v___x_229_ = lean_box(0);
v___x_230_ = lean_apply_2(v_toPure_228_, lean_box(0), v___x_229_);
return v___x_230_;
}
else
{
lean_object* v_toFunctor_231_; lean_object* v_val_232_; lean_object* v_map_233_; lean_object* v___f_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_toFunctor_231_ = lean_ctor_get(v_inst_225_, 0);
lean_inc_ref(v_toFunctor_231_);
lean_dec_ref(v_inst_225_);
v_val_232_ = lean_ctor_get(v_a_227_, 0);
lean_inc(v_val_232_);
lean_dec_ref(v_a_227_);
v_map_233_ = lean_ctor_get(v_toFunctor_231_, 0);
lean_inc(v_map_233_);
lean_dec_ref(v_toFunctor_231_);
v___f_234_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_235_ = lean_apply_1(v_f_226_, v_val_232_);
v___x_236_ = lean_apply_4(v_map_233_, lean_box(0), lean_box(0), v___f_234_, v___x_235_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Option_filterM___redArg___lam__0(lean_object* v_x_237_, uint8_t v_b_238_){
_start:
{
if (v_b_238_ == 0)
{
lean_object* v___x_239_; 
v___x_239_ = lean_box(0);
return v___x_239_;
}
else
{
lean_inc(v_x_237_);
return v_x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Option_filterM___redArg___lam__0___boxed(lean_object* v_x_240_, lean_object* v_b_241_){
_start:
{
uint8_t v_b_boxed_242_; lean_object* v_res_243_; 
v_b_boxed_242_ = lean_unbox(v_b_241_);
v_res_243_ = l_Option_filterM___redArg___lam__0(v_x_240_, v_b_boxed_242_);
lean_dec(v_x_240_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Option_filterM___redArg(lean_object* v_inst_244_, lean_object* v_p_245_, lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
lean_object* v_toPure_247_; lean_object* v___x_248_; 
lean_dec(v_p_245_);
v_toPure_247_ = lean_ctor_get(v_inst_244_, 1);
lean_inc(v_toPure_247_);
lean_dec_ref(v_inst_244_);
v___x_248_ = lean_apply_2(v_toPure_247_, lean_box(0), v_x_246_);
return v___x_248_;
}
else
{
lean_object* v_toFunctor_249_; lean_object* v_val_250_; lean_object* v_map_251_; lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_toFunctor_249_ = lean_ctor_get(v_inst_244_, 0);
lean_inc_ref(v_toFunctor_249_);
lean_dec_ref(v_inst_244_);
v_val_250_ = lean_ctor_get(v_x_246_, 0);
lean_inc(v_val_250_);
v_map_251_ = lean_ctor_get(v_toFunctor_249_, 0);
lean_inc(v_map_251_);
lean_dec_ref(v_toFunctor_249_);
v___f_252_ = lean_alloc_closure((void*)(l_Option_filterM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_252_, 0, v_x_246_);
v___x_253_ = lean_apply_1(v_p_245_, v_val_250_);
v___x_254_ = lean_apply_4(v_map_251_, lean_box(0), lean_box(0), v___f_252_, v___x_253_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Option_filterM(lean_object* v_m_255_, lean_object* v_00_u03b1_256_, lean_object* v_inst_257_, lean_object* v_p_258_, lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v_toPure_260_; lean_object* v___x_261_; 
lean_dec(v_p_258_);
v_toPure_260_ = lean_ctor_get(v_inst_257_, 1);
lean_inc(v_toPure_260_);
lean_dec_ref(v_inst_257_);
v___x_261_ = lean_apply_2(v_toPure_260_, lean_box(0), v_x_259_);
return v___x_261_;
}
else
{
lean_object* v_toFunctor_262_; lean_object* v_val_263_; lean_object* v_map_264_; lean_object* v___f_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_toFunctor_262_ = lean_ctor_get(v_inst_257_, 0);
lean_inc_ref(v_toFunctor_262_);
lean_dec_ref(v_inst_257_);
v_val_263_ = lean_ctor_get(v_x_259_, 0);
lean_inc(v_val_263_);
v_map_264_ = lean_ctor_get(v_toFunctor_262_, 0);
lean_inc(v_map_264_);
lean_dec_ref(v_toFunctor_262_);
v___f_265_ = lean_alloc_closure((void*)(l_Option_filterM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_265_, 0, v_x_259_);
v___x_266_ = lean_apply_1(v_p_258_, v_val_263_);
v___x_267_ = lean_apply_4(v_map_264_, lean_box(0), lean_box(0), v___f_265_, v___x_266_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l_Option_filter___redArg(lean_object* v_p_268_, lean_object* v_x_269_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
lean_dec_ref(v_p_268_);
return v_x_269_;
}
else
{
lean_object* v_val_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_val_270_ = lean_ctor_get(v_x_269_, 0);
lean_inc(v_val_270_);
v___x_271_ = lean_apply_1(v_p_268_, v_val_270_);
v___x_272_ = lean_unbox(v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
lean_dec_ref(v_x_269_);
v___x_273_ = lean_box(0);
return v___x_273_;
}
else
{
return v_x_269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_filter(lean_object* v_00_u03b1_274_, lean_object* v_p_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
lean_dec_ref(v_p_275_);
return v_x_276_;
}
else
{
lean_object* v_val_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_val_277_ = lean_ctor_get(v_x_276_, 0);
lean_inc(v_val_277_);
v___x_278_ = lean_apply_1(v_p_275_, v_val_277_);
v___x_279_ = lean_unbox(v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
lean_dec_ref(v_x_276_);
v___x_280_ = lean_box(0);
return v___x_280_;
}
else
{
return v_x_276_;
}
}
}
}
LEAN_EXPORT uint8_t l_Option_all___redArg(lean_object* v_p_281_, lean_object* v_x_282_){
_start:
{
if (lean_obj_tag(v_x_282_) == 0)
{
uint8_t v___x_283_; 
lean_dec_ref(v_p_281_);
v___x_283_ = 1;
return v___x_283_;
}
else
{
lean_object* v_val_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_val_284_ = lean_ctor_get(v_x_282_, 0);
lean_inc(v_val_284_);
lean_dec_ref(v_x_282_);
v___x_285_ = lean_apply_1(v_p_281_, v_val_284_);
v___x_286_ = lean_unbox(v___x_285_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_Option_all___redArg___boxed(lean_object* v_p_287_, lean_object* v_x_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Option_all___redArg(v_p_287_, v_x_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT uint8_t l_Option_all(lean_object* v_00_u03b1_291_, lean_object* v_p_292_, lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
uint8_t v___x_294_; 
lean_dec_ref(v_p_292_);
v___x_294_ = 1;
return v___x_294_;
}
else
{
lean_object* v_val_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_val_295_ = lean_ctor_get(v_x_293_, 0);
lean_inc(v_val_295_);
lean_dec_ref(v_x_293_);
v___x_296_ = lean_apply_1(v_p_292_, v_val_295_);
v___x_297_ = lean_unbox(v___x_296_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Option_all___boxed(lean_object* v_00_u03b1_298_, lean_object* v_p_299_, lean_object* v_x_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Option_all(v_00_u03b1_298_, v_p_299_, v_x_300_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint8_t l_Option_any___redArg(lean_object* v_p_303_, lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
uint8_t v___x_305_; 
lean_dec_ref(v_p_303_);
v___x_305_ = 0;
return v___x_305_;
}
else
{
lean_object* v_val_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_val_306_ = lean_ctor_get(v_x_304_, 0);
lean_inc(v_val_306_);
lean_dec_ref(v_x_304_);
v___x_307_ = lean_apply_1(v_p_303_, v_val_306_);
v___x_308_ = lean_unbox(v___x_307_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l_Option_any___redArg___boxed(lean_object* v_p_309_, lean_object* v_x_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_Option_any___redArg(v_p_309_, v_x_310_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT uint8_t l_Option_any(lean_object* v_00_u03b1_313_, lean_object* v_p_314_, lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
uint8_t v___x_316_; 
lean_dec_ref(v_p_314_);
v___x_316_ = 0;
return v___x_316_;
}
else
{
lean_object* v_val_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v_val_317_ = lean_ctor_get(v_x_315_, 0);
lean_inc(v_val_317_);
lean_dec_ref(v_x_315_);
v___x_318_ = lean_apply_1(v_p_314_, v_val_317_);
v___x_319_ = lean_unbox(v___x_318_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Option_any___boxed(lean_object* v_00_u03b1_320_, lean_object* v_p_321_, lean_object* v_x_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Option_any(v_00_u03b1_320_, v_p_321_, v_x_322_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse___lam__0(lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
if (lean_obj_tag(v_x_325_) == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_box(0);
v___x_328_ = lean_apply_1(v_x_326_, v___x_327_);
return v___x_328_;
}
else
{
lean_dec_ref(v_x_326_);
lean_inc_ref(v_x_325_);
return v_x_325_;
}
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse___lam__0___boxed(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Option_instOrElse___lam__0(v_x_329_, v_x_330_);
lean_dec(v_x_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse(lean_object* v_00_u03b1_333_){
_start:
{
lean_object* v___f_334_; 
v___f_334_ = ((lean_object*)(l_Option_instOrElse___closed__0));
return v___f_334_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableRelLt___redArg(lean_object* v_s_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_dec_ref(v_s_335_);
if (lean_obj_tag(v_x_337_) == 0)
{
uint8_t v___x_338_; 
v___x_338_ = 0;
return v___x_338_;
}
else
{
uint8_t v___x_339_; 
lean_dec_ref(v_x_337_);
v___x_339_ = 1;
return v___x_339_;
}
}
else
{
if (lean_obj_tag(v_x_337_) == 0)
{
uint8_t v___x_340_; 
lean_dec_ref(v_x_336_);
lean_dec_ref(v_s_335_);
v___x_340_ = 0;
return v___x_340_;
}
else
{
lean_object* v_val_341_; lean_object* v_val_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_val_341_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_val_341_);
lean_dec_ref(v_x_336_);
v_val_342_ = lean_ctor_get(v_x_337_, 0);
lean_inc(v_val_342_);
lean_dec_ref(v_x_337_);
v___x_343_ = lean_apply_2(v_s_335_, v_val_341_, v_val_342_);
v___x_344_ = lean_unbox(v___x_343_);
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___redArg___boxed(lean_object* v_s_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
uint8_t v_res_348_; lean_object* v_r_349_; 
v_res_348_ = l_Option_instDecidableRelLt___redArg(v_s_345_, v_x_346_, v_x_347_);
v_r_349_ = lean_box(v_res_348_);
return v_r_349_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableRelLt(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_r_352_, lean_object* v_s_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = l_Option_instDecidableRelLt___redArg(v_s_353_, v_x_354_, v_x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___boxed(lean_object* v_00_u03b1_357_, lean_object* v_00_u03b2_358_, lean_object* v_r_359_, lean_object* v_s_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
uint8_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_Option_instDecidableRelLt(v_00_u03b1_357_, v_00_u03b2_358_, v_r_359_, v_s_360_, v_x_361_, v_x_362_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT lean_object* l_Option_merge___redArg(lean_object* v_fn_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
if (lean_obj_tag(v_x_366_) == 0)
{
lean_dec(v_fn_365_);
return v_x_367_;
}
else
{
if (lean_obj_tag(v_x_367_) == 0)
{
lean_dec(v_fn_365_);
return v_x_366_;
}
else
{
lean_object* v_val_368_; lean_object* v_val_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_377_; 
v_val_368_ = lean_ctor_get(v_x_366_, 0);
lean_inc(v_val_368_);
lean_dec_ref(v_x_366_);
v_val_369_ = lean_ctor_get(v_x_367_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_x_367_);
if (v_isSharedCheck_377_ == 0)
{
v___x_371_ = v_x_367_;
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_val_369_);
lean_dec(v_x_367_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_apply_2(v_fn_365_, v_val_368_, v_val_369_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_merge(lean_object* v_00_u03b1_378_, lean_object* v_fn_379_, lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Option_merge___redArg(v_fn_379_, v_x_380_, v_x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Option_elim___redArg(lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
lean_dec(v_x_385_);
lean_inc(v_x_384_);
return v_x_384_;
}
else
{
lean_object* v_val_386_; lean_object* v___x_387_; 
v_val_386_ = lean_ctor_get(v_x_383_, 0);
lean_inc(v_val_386_);
lean_dec_ref(v_x_383_);
v___x_387_ = lean_apply_1(v_x_385_, v_val_386_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elim___redArg___boxed(lean_object* v_x_388_, lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Option_elim___redArg(v_x_388_, v_x_389_, v_x_390_);
lean_dec(v_x_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Option_elim(lean_object* v_00_u03b1_392_, lean_object* v_00_u03b2_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
lean_dec(v_x_396_);
lean_inc(v_x_395_);
return v_x_395_;
}
else
{
lean_object* v_val_397_; lean_object* v___x_398_; 
v_val_397_ = lean_ctor_get(v_x_394_, 0);
lean_inc(v_val_397_);
lean_dec_ref(v_x_394_);
v___x_398_ = lean_apply_1(v_x_396_, v_val_397_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elim___boxed(lean_object* v_00_u03b1_399_, lean_object* v_00_u03b2_400_, lean_object* v_x_401_, lean_object* v_x_402_, lean_object* v_x_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Option_elim(v_00_u03b1_399_, v_00_u03b2_400_, v_x_401_, v_x_402_, v_x_403_);
lean_dec(v_x_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Option_get___redArg(lean_object* v_x_405_){
_start:
{
lean_object* v_val_406_; 
v_val_406_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_val_406_);
return v_val_406_;
}
}
LEAN_EXPORT lean_object* l_Option_get___redArg___boxed(lean_object* v_x_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Option_get___redArg(v_x_407_);
lean_dec(v_x_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Option_get(lean_object* v_00_u03b1_409_, lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
lean_object* v_val_412_; 
v_val_412_ = lean_ctor_get(v_x_410_, 0);
lean_inc(v_val_412_);
return v_val_412_;
}
}
LEAN_EXPORT lean_object* l_Option_get___boxed(lean_object* v_00_u03b1_413_, lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Option_get(v_00_u03b1_413_, v_x_414_, v_x_415_);
lean_dec(v_x_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Option_guard___redArg(lean_object* v_p_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_419_; uint8_t v___x_420_; 
lean_inc(v_a_418_);
v___x_419_ = lean_apply_1(v_p_417_, v_a_418_);
v___x_420_ = lean_unbox(v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_dec(v_a_418_);
v___x_421_ = lean_box(0);
return v___x_421_;
}
else
{
lean_object* v___x_422_; 
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v_a_418_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Option_guard(lean_object* v_00_u03b1_423_, lean_object* v_p_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_426_; uint8_t v___x_427_; 
lean_inc(v_a_425_);
v___x_426_ = lean_apply_1(v_p_424_, v_a_425_);
v___x_427_ = lean_unbox(v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec(v_a_425_);
v___x_428_ = lean_box(0);
return v___x_428_;
}
else
{
lean_object* v___x_429_; 
v___x_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_429_, 0, v_a_425_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toList___redArg(lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
lean_object* v___x_431_; 
v___x_431_ = lean_box(0);
return v___x_431_;
}
else
{
lean_object* v_val_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_val_432_ = lean_ctor_get(v_x_430_, 0);
v___x_433_ = lean_box(0);
lean_inc(v_val_432_);
v___x_434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_434_, 0, v_val_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toList___redArg___boxed(lean_object* v_x_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Option_toList___redArg(v_x_435_);
lean_dec(v_x_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Option_toList(lean_object* v_00_u03b1_437_, lean_object* v_x_438_){
_start:
{
if (lean_obj_tag(v_x_438_) == 0)
{
lean_object* v___x_439_; 
v___x_439_ = lean_box(0);
return v___x_439_;
}
else
{
lean_object* v_val_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_val_440_ = lean_ctor_get(v_x_438_, 0);
v___x_441_ = lean_box(0);
lean_inc(v_val_440_);
v___x_442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_442_, 0, v_val_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toList___boxed(lean_object* v_00_u03b1_443_, lean_object* v_x_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Option_toList(v_00_u03b1_443_, v_x_444_);
lean_dec(v_x_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Option_toArray___redArg(lean_object* v_x_448_){
_start:
{
if (lean_obj_tag(v_x_448_) == 0)
{
lean_object* v___x_449_; 
v___x_449_ = ((lean_object*)(l_Option_toArray___redArg___closed__0));
return v___x_449_;
}
else
{
lean_object* v_val_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_val_450_ = lean_ctor_get(v_x_448_, 0);
lean_inc(v_val_450_);
lean_dec_ref(v_x_448_);
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_mk_empty_array_with_capacity(v___x_451_);
v___x_453_ = lean_array_push(v___x_452_, v_val_450_);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toArray(lean_object* v_00_u03b1_454_, lean_object* v_x_455_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
lean_object* v___x_456_; 
v___x_456_ = ((lean_object*)(l_Option_toArray___redArg___closed__0));
return v___x_456_;
}
else
{
lean_object* v_val_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_val_457_ = lean_ctor_get(v_x_455_, 0);
lean_inc(v_val_457_);
lean_dec_ref(v_x_455_);
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_mk_empty_array_with_capacity(v___x_458_);
v___x_460_ = lean_array_push(v___x_459_, v_val_457_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_Option_join___redArg(lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_object* v___x_462_; 
v___x_462_ = lean_box(0);
return v___x_462_;
}
else
{
lean_object* v_val_463_; 
v_val_463_ = lean_ctor_get(v_x_461_, 0);
lean_inc(v_val_463_);
return v_val_463_;
}
}
}
LEAN_EXPORT lean_object* l_Option_join___redArg___boxed(lean_object* v_x_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Option_join___redArg(v_x_464_);
lean_dec(v_x_464_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Option_join(lean_object* v_00_u03b1_466_, lean_object* v_x_467_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
lean_object* v___x_468_; 
v___x_468_ = lean_box(0);
return v___x_468_;
}
else
{
lean_object* v_val_469_; 
v_val_469_ = lean_ctor_get(v_x_467_, 0);
lean_inc(v_val_469_);
return v_val_469_;
}
}
}
LEAN_EXPORT lean_object* l_Option_join___boxed(lean_object* v_00_u03b1_470_, lean_object* v_x_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Option_join(v_00_u03b1_470_, v_x_471_);
lean_dec(v_x_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Option_sequence___redArg(lean_object* v_inst_473_, lean_object* v_x_474_){
_start:
{
if (lean_obj_tag(v_x_474_) == 0)
{
lean_object* v_toPure_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_toPure_475_ = lean_ctor_get(v_inst_473_, 1);
lean_inc(v_toPure_475_);
lean_dec_ref(v_inst_473_);
v___x_476_ = lean_box(0);
v___x_477_ = lean_apply_2(v_toPure_475_, lean_box(0), v___x_476_);
return v___x_477_;
}
else
{
lean_object* v_toFunctor_478_; lean_object* v_val_479_; lean_object* v_map_480_; lean_object* v___f_481_; lean_object* v___x_482_; 
v_toFunctor_478_ = lean_ctor_get(v_inst_473_, 0);
lean_inc_ref(v_toFunctor_478_);
lean_dec_ref(v_inst_473_);
v_val_479_ = lean_ctor_get(v_x_474_, 0);
lean_inc(v_val_479_);
lean_dec_ref(v_x_474_);
v_map_480_ = lean_ctor_get(v_toFunctor_478_, 0);
lean_inc(v_map_480_);
lean_dec_ref(v_toFunctor_478_);
v___f_481_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_482_ = lean_apply_4(v_map_480_, lean_box(0), lean_box(0), v___f_481_, v_val_479_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_Option_sequence(lean_object* v_m_483_, lean_object* v_inst_484_, lean_object* v_00_u03b1_485_, lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_486_) == 0)
{
lean_object* v_toPure_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_toPure_487_ = lean_ctor_get(v_inst_484_, 1);
lean_inc(v_toPure_487_);
lean_dec_ref(v_inst_484_);
v___x_488_ = lean_box(0);
v___x_489_ = lean_apply_2(v_toPure_487_, lean_box(0), v___x_488_);
return v___x_489_;
}
else
{
lean_object* v_toFunctor_490_; lean_object* v_val_491_; lean_object* v_map_492_; lean_object* v___f_493_; lean_object* v___x_494_; 
v_toFunctor_490_ = lean_ctor_get(v_inst_484_, 0);
lean_inc_ref(v_toFunctor_490_);
lean_dec_ref(v_inst_484_);
v_val_491_ = lean_ctor_get(v_x_486_, 0);
lean_inc(v_val_491_);
lean_dec_ref(v_x_486_);
v_map_492_ = lean_ctor_get(v_toFunctor_490_, 0);
lean_inc(v_map_492_);
lean_dec_ref(v_toFunctor_490_);
v___f_493_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_494_ = lean_apply_4(v_map_492_, lean_box(0), lean_box(0), v___f_493_, v_val_491_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elimM___redArg___lam__0(lean_object* v_y_495_, lean_object* v_z_496_, lean_object* v_____do__lift_497_){
_start:
{
if (lean_obj_tag(v_____do__lift_497_) == 0)
{
lean_dec(v_z_496_);
lean_inc(v_y_495_);
return v_y_495_;
}
else
{
lean_object* v_val_498_; lean_object* v___x_499_; 
v_val_498_ = lean_ctor_get(v_____do__lift_497_, 0);
lean_inc(v_val_498_);
lean_dec_ref(v_____do__lift_497_);
v___x_499_ = lean_apply_1(v_z_496_, v_val_498_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elimM___redArg___lam__0___boxed(lean_object* v_y_500_, lean_object* v_z_501_, lean_object* v_____do__lift_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Option_elimM___redArg___lam__0(v_y_500_, v_z_501_, v_____do__lift_502_);
lean_dec(v_y_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Option_elimM___redArg(lean_object* v_inst_504_, lean_object* v_x_505_, lean_object* v_y_506_, lean_object* v_z_507_){
_start:
{
lean_object* v_toBind_508_; lean_object* v___f_509_; lean_object* v___x_510_; 
v_toBind_508_ = lean_ctor_get(v_inst_504_, 1);
lean_inc(v_toBind_508_);
lean_dec_ref(v_inst_504_);
v___f_509_ = lean_alloc_closure((void*)(l_Option_elimM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_509_, 0, v_y_506_);
lean_closure_set(v___f_509_, 1, v_z_507_);
v___x_510_ = lean_apply_4(v_toBind_508_, lean_box(0), lean_box(0), v_x_505_, v___f_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Option_elimM(lean_object* v_m_511_, lean_object* v_00_u03b1_512_, lean_object* v_00_u03b2_513_, lean_object* v_inst_514_, lean_object* v_x_515_, lean_object* v_y_516_, lean_object* v_z_517_){
_start:
{
lean_object* v_toBind_518_; lean_object* v___f_519_; lean_object* v___x_520_; 
v_toBind_518_ = lean_ctor_get(v_inst_514_, 1);
lean_inc(v_toBind_518_);
lean_dec_ref(v_inst_514_);
v___f_519_ = lean_alloc_closure((void*)(l_Option_elimM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_519_, 0, v_y_516_);
lean_closure_set(v___f_519_, 1, v_z_517_);
v___x_520_ = lean_apply_4(v_toBind_518_, lean_box(0), lean_box(0), v_x_515_, v___f_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Option_getDM___redArg(lean_object* v_inst_521_, lean_object* v_x_522_, lean_object* v_y_523_){
_start:
{
if (lean_obj_tag(v_x_522_) == 0)
{
lean_dec(v_inst_521_);
lean_inc(v_y_523_);
return v_y_523_;
}
else
{
lean_object* v_val_524_; lean_object* v___x_525_; 
v_val_524_ = lean_ctor_get(v_x_522_, 0);
lean_inc(v_val_524_);
lean_dec_ref(v_x_522_);
v___x_525_ = lean_apply_2(v_inst_521_, lean_box(0), v_val_524_);
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l_Option_getDM___redArg___boxed(lean_object* v_inst_526_, lean_object* v_x_527_, lean_object* v_y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Option_getDM___redArg(v_inst_526_, v_x_527_, v_y_528_);
lean_dec(v_y_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Option_getDM(lean_object* v_m_530_, lean_object* v_00_u03b1_531_, lean_object* v_inst_532_, lean_object* v_x_533_, lean_object* v_y_534_){
_start:
{
if (lean_obj_tag(v_x_533_) == 0)
{
lean_dec(v_inst_532_);
lean_inc(v_y_534_);
return v_y_534_;
}
else
{
lean_object* v_val_535_; lean_object* v___x_536_; 
v_val_535_ = lean_ctor_get(v_x_533_, 0);
lean_inc(v_val_535_);
lean_dec_ref(v_x_533_);
v___x_536_ = lean_apply_2(v_inst_532_, lean_box(0), v_val_535_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Option_getDM___boxed(lean_object* v_m_537_, lean_object* v_00_u03b1_538_, lean_object* v_inst_539_, lean_object* v_x_540_, lean_object* v_y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Option_getDM(v_m_537_, v_00_u03b1_538_, v_inst_539_, v_x_540_, v_y_541_);
lean_dec(v_y_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Option_min___redArg(lean_object* v_inst_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_dec(v_inst_543_);
if (lean_obj_tag(v_x_545_) == 0)
{
return v_x_545_;
}
else
{
lean_dec_ref(v_x_545_);
return v_x_544_;
}
}
else
{
if (lean_obj_tag(v_x_545_) == 0)
{
lean_dec_ref(v_x_544_);
lean_dec(v_inst_543_);
return v_x_545_;
}
else
{
lean_object* v_val_546_; lean_object* v_val_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
v_val_546_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_val_546_);
lean_dec_ref(v_x_544_);
v_val_547_ = lean_ctor_get(v_x_545_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_555_ == 0)
{
v___x_549_ = v_x_545_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_val_547_);
lean_dec(v_x_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_apply_2(v_inst_543_, v_val_546_, v_val_547_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_min(lean_object* v_00_u03b1_556_, lean_object* v_inst_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Option_min___redArg(v_inst_557_, v_x_558_, v_x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Option_instMin___redArg(lean_object* v_inst_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = lean_alloc_closure((void*)(l_Option_min), 4, 2);
lean_closure_set(v___x_562_, 0, lean_box(0));
lean_closure_set(v___x_562_, 1, v_inst_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Option_instMin(lean_object* v_00_u03b1_563_, lean_object* v_inst_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_closure((void*)(l_Option_min), 4, 2);
lean_closure_set(v___x_565_, 0, lean_box(0));
lean_closure_set(v___x_565_, 1, v_inst_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Option_max___redArg(lean_object* v_inst_566_, lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
lean_dec(v_inst_566_);
return v_x_568_;
}
else
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_dec(v_inst_566_);
return v_x_567_;
}
else
{
lean_object* v_val_569_; lean_object* v_val_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_578_; 
v_val_569_ = lean_ctor_get(v_x_567_, 0);
lean_inc(v_val_569_);
lean_dec_ref(v_x_567_);
v_val_570_ = lean_ctor_get(v_x_568_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v_x_568_);
if (v_isSharedCheck_578_ == 0)
{
v___x_572_ = v_x_568_;
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_val_570_);
lean_dec(v_x_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_574_ = lean_apply_2(v_inst_566_, v_val_569_, v_val_570_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_574_);
v___x_576_ = v___x_572_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_max(lean_object* v_00_u03b1_579_, lean_object* v_inst_580_, lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Option_max___redArg(v_inst_580_, v_x_581_, v_x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Option_instMax___redArg(lean_object* v_inst_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lean_alloc_closure((void*)(l_Option_max), 4, 2);
lean_closure_set(v___x_585_, 0, lean_box(0));
lean_closure_set(v___x_585_, 1, v_inst_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Option_instMax(lean_object* v_00_u03b1_586_, lean_object* v_inst_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = lean_alloc_closure((void*)(l_Option_max), 4, 2);
lean_closure_set(v___x_588_, 0, lean_box(0));
lean_closure_set(v___x_588_, 1, v_inst_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_instLTOption(lean_object* v_00_u03b1_589_, lean_object* v_inst_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = lean_box(0);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_instLEOption(lean_object* v_00_u03b1_592_, lean_object* v_inst_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_box(0);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_instFunctorOption___lam__0(lean_object* v_00_u03b1_595_, lean_object* v_00_u03b2_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
if (lean_obj_tag(v___y_598_) == 0)
{
lean_object* v___x_599_; 
lean_dec(v___y_597_);
v___x_599_ = lean_box(0);
return v___x_599_;
}
else
{
lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_isSharedCheck_606_ = !lean_is_exclusive(v___y_598_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___y_598_, 0);
lean_dec(v_unused_607_);
v___x_601_ = v___y_598_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_dec(v___y_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___y_597_);
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___y_597_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__0(lean_object* v_00_u03b1_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v___y_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__1(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_f_619_, lean_object* v_x_620_){
_start:
{
if (lean_obj_tag(v_f_619_) == 0)
{
lean_object* v___x_621_; 
lean_dec_ref(v_x_620_);
v___x_621_ = lean_box(0);
return v___x_621_;
}
else
{
lean_object* v_val_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_val_622_ = lean_ctor_get(v_f_619_, 0);
lean_inc(v_val_622_);
lean_dec_ref(v_f_619_);
v___x_623_ = lean_box(0);
v___x_624_ = lean_apply_1(v_x_620_, v___x_623_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v___x_625_; 
lean_dec(v_val_622_);
v___x_625_ = lean_box(0);
return v___x_625_;
}
else
{
lean_object* v_val_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_634_; 
v_val_626_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_634_ == 0)
{
v___x_628_ = v___x_624_;
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_val_626_);
lean_dec(v___x_624_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_apply_1(v_val_622_, v_val_626_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__2(lean_object* v_00_u03b1_635_, lean_object* v_00_u03b2_636_, lean_object* v_x_637_, lean_object* v_y_638_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_dec_ref(v_y_638_);
return v_x_637_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_box(0);
v___x_640_ = lean_apply_1(v_y_638_, v___x_639_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v___x_641_; 
v___x_641_ = lean_box(0);
return v___x_641_;
}
else
{
lean_dec_ref(v___x_640_);
lean_inc_ref(v_x_637_);
return v_x_637_;
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__2___boxed(lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_x_644_, lean_object* v_y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_instMonadOption___lam__2(v_00_u03b1_642_, v_00_u03b2_643_, v_x_644_, v_y_645_);
lean_dec(v_x_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__3(lean_object* v_00_u03b1_647_, lean_object* v_00_u03b2_648_, lean_object* v_x_649_, lean_object* v_y_650_){
_start:
{
if (lean_obj_tag(v_x_649_) == 0)
{
lean_object* v___x_651_; 
lean_dec_ref(v_y_650_);
v___x_651_ = lean_box(0);
return v___x_651_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_box(0);
v___x_653_ = lean_apply_1(v_y_650_, v___x_652_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__3___boxed(lean_object* v_00_u03b1_654_, lean_object* v_00_u03b2_655_, lean_object* v_x_656_, lean_object* v_y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_instMonadOption___lam__3(v_00_u03b1_654_, v_00_u03b2_655_, v_x_656_, v_y_657_);
lean_dec(v_x_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__0(lean_object* v_00_u03b1_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = lean_box(0);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__1(lean_object* v_00_u03b1_676_, lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
if (lean_obj_tag(v_x_677_) == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_box(0);
v___x_680_ = lean_apply_1(v_x_678_, v___x_679_);
return v___x_680_;
}
else
{
lean_dec_ref(v_x_678_);
lean_inc_ref(v_x_677_);
return v_x_677_;
}
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__1___boxed(lean_object* v_00_u03b1_681_, lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_instAlternativeOption___lam__1(v_00_u03b1_681_, v_x_682_, v_x_683_);
lean_dec(v_x_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_liftOption___redArg(lean_object* v_inst_692_, lean_object* v_x_693_){
_start:
{
if (lean_obj_tag(v_x_693_) == 0)
{
lean_object* v_failure_694_; lean_object* v___x_695_; 
v_failure_694_ = lean_ctor_get(v_inst_692_, 1);
lean_inc(v_failure_694_);
lean_dec_ref(v_inst_692_);
v___x_695_ = lean_apply_1(v_failure_694_, lean_box(0));
return v___x_695_;
}
else
{
lean_object* v_toApplicative_696_; lean_object* v_toPure_697_; lean_object* v_val_698_; lean_object* v___x_699_; 
v_toApplicative_696_ = lean_ctor_get(v_inst_692_, 0);
lean_inc_ref(v_toApplicative_696_);
lean_dec_ref(v_inst_692_);
v_toPure_697_ = lean_ctor_get(v_toApplicative_696_, 1);
lean_inc(v_toPure_697_);
lean_dec_ref(v_toApplicative_696_);
v_val_698_ = lean_ctor_get(v_x_693_, 0);
lean_inc(v_val_698_);
lean_dec_ref(v_x_693_);
v___x_699_ = lean_apply_2(v_toPure_697_, lean_box(0), v_val_698_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_liftOption(lean_object* v_m_700_, lean_object* v_00_u03b1_701_, lean_object* v_inst_702_, lean_object* v_x_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_liftOption___redArg(v_inst_702_, v_x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___redArg(lean_object* v_x_705_, lean_object* v_handle_706_){
_start:
{
if (lean_obj_tag(v_x_705_) == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_box(0);
v___x_708_ = lean_apply_1(v_handle_706_, v___x_707_);
return v___x_708_;
}
else
{
lean_dec_ref(v_handle_706_);
lean_inc_ref(v_x_705_);
return v_x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___redArg___boxed(lean_object* v_x_709_, lean_object* v_handle_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Option_tryCatch___redArg(v_x_709_, v_handle_710_);
lean_dec(v_x_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch(lean_object* v_00_u03b1_712_, lean_object* v_x_713_, lean_object* v_handle_714_){
_start:
{
if (lean_obj_tag(v_x_713_) == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_box(0);
v___x_716_ = lean_apply_1(v_handle_714_, v___x_715_);
return v___x_716_;
}
else
{
lean_dec_ref(v_handle_714_);
lean_inc_ref(v_x_713_);
return v_x_713_;
}
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___boxed(lean_object* v_00_u03b1_717_, lean_object* v_x_718_, lean_object* v_handle_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Option_tryCatch(v_00_u03b1_717_, v_x_718_, v_handle_719_);
lean_dec(v_x_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption___lam__0(lean_object* v_00_u03b1_721_, lean_object* v_x_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = lean_box(0);
return v___x_723_;
}
}
lean_object* runtime_initialize_Init_Control_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Option_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
