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
lean_dec_ref_known(v_x_55_, 1);
v___x_57_ = 0;
return v___x_57_;
}
}
else
{
if (lean_obj_tag(v_x_55_) == 0)
{
uint8_t v___x_58_; 
lean_dec_ref_known(v_x_54_, 1);
lean_dec_ref(v_inst_53_);
v___x_58_ = 0;
return v___x_58_;
}
else
{
lean_object* v_val_59_; lean_object* v_val_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_val_59_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_val_59_);
lean_dec_ref_known(v_x_54_, 1);
v_val_60_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_val_60_);
lean_dec_ref_known(v_x_55_, 1);
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
lean_dec_ref_known(v_x_85_, 1);
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
lean_dec_ref_known(v_x_126_, 1);
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
lean_dec_ref_known(v_x_139_, 1);
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
lean_dec_ref_known(v_x_151_, 1);
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
lean_dec_ref_known(v_x_158_, 1);
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
lean_dec_ref_known(v_x_165_, 1);
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
lean_dec_ref_known(v_x_175_, 1);
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
lean_dec_ref_known(v_x_185_, 1);
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
lean_dec_ref_known(v_x_200_, 1);
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
lean_dec_ref_known(v_a_212_, 1);
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
lean_dec_ref_known(v_a_227_, 1);
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
lean_dec_ref_known(v_x_269_, 1);
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
lean_dec_ref_known(v_x_276_, 1);
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
lean_dec_ref_known(v_x_282_, 1);
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
lean_dec_ref_known(v_x_293_, 1);
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
lean_dec_ref_known(v_x_304_, 1);
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
lean_dec_ref_known(v_x_315_, 1);
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
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg___lam__0(lean_object* v_x_325_, lean_object* v_x_326_){
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
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg___lam__0___boxed(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Option_instOrElse___redArg___lam__0(v_x_329_, v_x_330_);
lean_dec(v_x_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg(){
_start:
{
lean_object* v___f_334_; 
v___f_334_ = ((lean_object*)(l_Option_instOrElse___redArg___closed__0));
return v___f_334_;
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse___redArg___boxed(lean_object* v___dummy_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Option_instOrElse___redArg();
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Option_instOrElse(lean_object* v_00_u03b1_337_){
_start:
{
lean_object* v___f_338_; 
v___f_338_ = ((lean_object*)(l_Option_instOrElse___redArg___closed__0));
return v___f_338_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableRelLt___redArg(lean_object* v_s_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
lean_dec_ref(v_s_339_);
if (lean_obj_tag(v_x_341_) == 0)
{
uint8_t v___x_342_; 
v___x_342_ = 0;
return v___x_342_;
}
else
{
uint8_t v___x_343_; 
lean_dec_ref_known(v_x_341_, 1);
v___x_343_ = 1;
return v___x_343_;
}
}
else
{
if (lean_obj_tag(v_x_341_) == 0)
{
uint8_t v___x_344_; 
lean_dec_ref_known(v_x_340_, 1);
lean_dec_ref(v_s_339_);
v___x_344_ = 0;
return v___x_344_;
}
else
{
lean_object* v_val_345_; lean_object* v_val_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_val_345_ = lean_ctor_get(v_x_340_, 0);
lean_inc(v_val_345_);
lean_dec_ref_known(v_x_340_, 1);
v_val_346_ = lean_ctor_get(v_x_341_, 0);
lean_inc(v_val_346_);
lean_dec_ref_known(v_x_341_, 1);
v___x_347_ = lean_apply_2(v_s_339_, v_val_345_, v_val_346_);
v___x_348_ = lean_unbox(v___x_347_);
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___redArg___boxed(lean_object* v_s_349_, lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_Option_instDecidableRelLt___redArg(v_s_349_, v_x_350_, v_x_351_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableRelLt(lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_r_356_, lean_object* v_s_357_, lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
uint8_t v___x_360_; 
v___x_360_ = l_Option_instDecidableRelLt___redArg(v_s_357_, v_x_358_, v_x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLt___boxed(lean_object* v_00_u03b1_361_, lean_object* v_00_u03b2_362_, lean_object* v_r_363_, lean_object* v_s_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_Option_instDecidableRelLt(v_00_u03b1_361_, v_00_u03b2_362_, v_r_363_, v_s_364_, v_x_365_, v_x_366_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableRelLe___redArg(lean_object* v_s_369_, lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
if (lean_obj_tag(v_x_370_) == 0)
{
uint8_t v___x_372_; 
lean_dec(v_x_371_);
lean_dec_ref(v_s_369_);
v___x_372_ = 1;
return v___x_372_;
}
else
{
if (lean_obj_tag(v_x_371_) == 0)
{
uint8_t v___x_373_; 
lean_dec_ref_known(v_x_370_, 1);
lean_dec_ref(v_s_369_);
v___x_373_ = 0;
return v___x_373_;
}
else
{
lean_object* v_val_374_; lean_object* v_val_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_val_374_ = lean_ctor_get(v_x_370_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v_x_370_, 1);
v_val_375_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_val_375_);
lean_dec_ref_known(v_x_371_, 1);
v___x_376_ = lean_apply_2(v_s_369_, v_val_374_, v_val_375_);
v___x_377_ = lean_unbox(v___x_376_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLe___redArg___boxed(lean_object* v_s_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l_Option_instDecidableRelLe___redArg(v_s_378_, v_x_379_, v_x_380_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT uint8_t l_Option_instDecidableRelLe(lean_object* v_00_u03b1_383_, lean_object* v_00_u03b2_384_, lean_object* v_r_385_, lean_object* v_s_386_, lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = l_Option_instDecidableRelLe___redArg(v_s_386_, v_x_387_, v_x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Option_instDecidableRelLe___boxed(lean_object* v_00_u03b1_390_, lean_object* v_00_u03b2_391_, lean_object* v_r_392_, lean_object* v_s_393_, lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Option_instDecidableRelLe(v_00_u03b1_390_, v_00_u03b2_391_, v_r_392_, v_s_393_, v_x_394_, v_x_395_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT lean_object* l_Option_merge___redArg(lean_object* v_fn_398_, lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
lean_dec(v_fn_398_);
return v_x_400_;
}
else
{
if (lean_obj_tag(v_x_400_) == 0)
{
lean_dec(v_fn_398_);
return v_x_399_;
}
else
{
lean_object* v_val_401_; lean_object* v_val_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_410_; 
v_val_401_ = lean_ctor_get(v_x_399_, 0);
lean_inc(v_val_401_);
lean_dec_ref_known(v_x_399_, 1);
v_val_402_ = lean_ctor_get(v_x_400_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v_x_400_);
if (v_isSharedCheck_410_ == 0)
{
v___x_404_ = v_x_400_;
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_val_402_);
lean_dec(v_x_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_apply_2(v_fn_398_, v_val_401_, v_val_402_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_406_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_merge(lean_object* v_00_u03b1_411_, lean_object* v_fn_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Option_merge___redArg(v_fn_412_, v_x_413_, v_x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Option_elim___redArg(lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
if (lean_obj_tag(v_x_416_) == 0)
{
lean_dec(v_x_418_);
lean_inc(v_x_417_);
return v_x_417_;
}
else
{
lean_object* v_val_419_; lean_object* v___x_420_; 
v_val_419_ = lean_ctor_get(v_x_416_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v_x_416_, 1);
v___x_420_ = lean_apply_1(v_x_418_, v_val_419_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elim___redArg___boxed(lean_object* v_x_421_, lean_object* v_x_422_, lean_object* v_x_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Option_elim___redArg(v_x_421_, v_x_422_, v_x_423_);
lean_dec(v_x_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Option_elim(lean_object* v_00_u03b1_425_, lean_object* v_00_u03b2_426_, lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
lean_dec(v_x_429_);
lean_inc(v_x_428_);
return v_x_428_;
}
else
{
lean_object* v_val_430_; lean_object* v___x_431_; 
v_val_430_ = lean_ctor_get(v_x_427_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v_x_427_, 1);
v___x_431_ = lean_apply_1(v_x_429_, v_val_430_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elim___boxed(lean_object* v_00_u03b1_432_, lean_object* v_00_u03b2_433_, lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Option_elim(v_00_u03b1_432_, v_00_u03b2_433_, v_x_434_, v_x_435_, v_x_436_);
lean_dec(v_x_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Option_get___redArg(lean_object* v_x_438_){
_start:
{
lean_object* v_val_439_; 
v_val_439_ = lean_ctor_get(v_x_438_, 0);
lean_inc(v_val_439_);
return v_val_439_;
}
}
LEAN_EXPORT lean_object* l_Option_get___redArg___boxed(lean_object* v_x_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Option_get___redArg(v_x_440_);
lean_dec(v_x_440_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Option_get(lean_object* v_00_u03b1_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
lean_object* v_val_445_; 
v_val_445_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_val_445_);
return v_val_445_;
}
}
LEAN_EXPORT lean_object* l_Option_get___boxed(lean_object* v_00_u03b1_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Option_get(v_00_u03b1_446_, v_x_447_, v_x_448_);
lean_dec(v_x_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Option_guard___redArg(lean_object* v_p_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_452_; uint8_t v___x_453_; 
lean_inc(v_a_451_);
v___x_452_ = lean_apply_1(v_p_450_, v_a_451_);
v___x_453_ = lean_unbox(v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
lean_dec(v_a_451_);
v___x_454_ = lean_box(0);
return v___x_454_;
}
else
{
lean_object* v___x_455_; 
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v_a_451_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l_Option_guard(lean_object* v_00_u03b1_456_, lean_object* v_p_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_459_; uint8_t v___x_460_; 
lean_inc(v_a_458_);
v___x_459_ = lean_apply_1(v_p_457_, v_a_458_);
v___x_460_ = lean_unbox(v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_dec(v_a_458_);
v___x_461_ = lean_box(0);
return v___x_461_;
}
else
{
lean_object* v___x_462_; 
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v_a_458_);
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toList___redArg(lean_object* v_x_463_){
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
lean_object* v_val_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_val_465_ = lean_ctor_get(v_x_463_, 0);
v___x_466_ = lean_box(0);
lean_inc(v_val_465_);
v___x_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_467_, 0, v_val_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toList___redArg___boxed(lean_object* v_x_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Option_toList___redArg(v_x_468_);
lean_dec(v_x_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Option_toList(lean_object* v_00_u03b1_470_, lean_object* v_x_471_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
lean_object* v___x_472_; 
v___x_472_ = lean_box(0);
return v___x_472_;
}
else
{
lean_object* v_val_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_val_473_ = lean_ctor_get(v_x_471_, 0);
v___x_474_ = lean_box(0);
lean_inc(v_val_473_);
v___x_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_475_, 0, v_val_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toList___boxed(lean_object* v_00_u03b1_476_, lean_object* v_x_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Option_toList(v_00_u03b1_476_, v_x_477_);
lean_dec(v_x_477_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Option_toArray___redArg(lean_object* v_x_481_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
lean_object* v___x_482_; 
v___x_482_ = ((lean_object*)(l_Option_toArray___redArg___closed__0));
return v___x_482_;
}
else
{
lean_object* v_val_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_val_483_ = lean_ctor_get(v_x_481_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v_x_481_, 1);
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_mk_empty_array_with_capacity(v___x_484_);
v___x_486_ = lean_array_push(v___x_485_, v_val_483_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toArray(lean_object* v_00_u03b1_487_, lean_object* v_x_488_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
lean_object* v___x_489_; 
v___x_489_ = ((lean_object*)(l_Option_toArray___redArg___closed__0));
return v___x_489_;
}
else
{
lean_object* v_val_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_val_490_ = lean_ctor_get(v_x_488_, 0);
lean_inc(v_val_490_);
lean_dec_ref_known(v_x_488_, 1);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_mk_empty_array_with_capacity(v___x_491_);
v___x_493_ = lean_array_push(v___x_492_, v_val_490_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l_Option_join___redArg(lean_object* v_x_494_){
_start:
{
if (lean_obj_tag(v_x_494_) == 0)
{
lean_object* v___x_495_; 
v___x_495_ = lean_box(0);
return v___x_495_;
}
else
{
lean_object* v_val_496_; 
v_val_496_ = lean_ctor_get(v_x_494_, 0);
lean_inc(v_val_496_);
return v_val_496_;
}
}
}
LEAN_EXPORT lean_object* l_Option_join___redArg___boxed(lean_object* v_x_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Option_join___redArg(v_x_497_);
lean_dec(v_x_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Option_join(lean_object* v_00_u03b1_499_, lean_object* v_x_500_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_object* v___x_501_; 
v___x_501_ = lean_box(0);
return v___x_501_;
}
else
{
lean_object* v_val_502_; 
v_val_502_ = lean_ctor_get(v_x_500_, 0);
lean_inc(v_val_502_);
return v_val_502_;
}
}
}
LEAN_EXPORT lean_object* l_Option_join___boxed(lean_object* v_00_u03b1_503_, lean_object* v_x_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Option_join(v_00_u03b1_503_, v_x_504_);
lean_dec(v_x_504_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Option_sequence___redArg(lean_object* v_inst_506_, lean_object* v_x_507_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v_toPure_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_toPure_508_ = lean_ctor_get(v_inst_506_, 1);
lean_inc(v_toPure_508_);
lean_dec_ref(v_inst_506_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_apply_2(v_toPure_508_, lean_box(0), v___x_509_);
return v___x_510_;
}
else
{
lean_object* v_toFunctor_511_; lean_object* v_val_512_; lean_object* v_map_513_; lean_object* v___f_514_; lean_object* v___x_515_; 
v_toFunctor_511_ = lean_ctor_get(v_inst_506_, 0);
lean_inc_ref(v_toFunctor_511_);
lean_dec_ref(v_inst_506_);
v_val_512_ = lean_ctor_get(v_x_507_, 0);
lean_inc(v_val_512_);
lean_dec_ref_known(v_x_507_, 1);
v_map_513_ = lean_ctor_get(v_toFunctor_511_, 0);
lean_inc(v_map_513_);
lean_dec_ref(v_toFunctor_511_);
v___f_514_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_515_ = lean_apply_4(v_map_513_, lean_box(0), lean_box(0), v___f_514_, v_val_512_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_Option_sequence(lean_object* v_m_516_, lean_object* v_inst_517_, lean_object* v_00_u03b1_518_, lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_519_) == 0)
{
lean_object* v_toPure_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_toPure_520_ = lean_ctor_get(v_inst_517_, 1);
lean_inc(v_toPure_520_);
lean_dec_ref(v_inst_517_);
v___x_521_ = lean_box(0);
v___x_522_ = lean_apply_2(v_toPure_520_, lean_box(0), v___x_521_);
return v___x_522_;
}
else
{
lean_object* v_toFunctor_523_; lean_object* v_val_524_; lean_object* v_map_525_; lean_object* v___f_526_; lean_object* v___x_527_; 
v_toFunctor_523_ = lean_ctor_get(v_inst_517_, 0);
lean_inc_ref(v_toFunctor_523_);
lean_dec_ref(v_inst_517_);
v_val_524_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_val_524_);
lean_dec_ref_known(v_x_519_, 1);
v_map_525_ = lean_ctor_get(v_toFunctor_523_, 0);
lean_inc(v_map_525_);
lean_dec_ref(v_toFunctor_523_);
v___f_526_ = ((lean_object*)(l_Option_mapM___redArg___closed__0));
v___x_527_ = lean_apply_4(v_map_525_, lean_box(0), lean_box(0), v___f_526_, v_val_524_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elimM___redArg___lam__0(lean_object* v_y_528_, lean_object* v_z_529_, lean_object* v_____do__lift_530_){
_start:
{
if (lean_obj_tag(v_____do__lift_530_) == 0)
{
lean_dec(v_z_529_);
lean_inc(v_y_528_);
return v_y_528_;
}
else
{
lean_object* v_val_531_; lean_object* v___x_532_; 
v_val_531_ = lean_ctor_get(v_____do__lift_530_, 0);
lean_inc(v_val_531_);
lean_dec_ref_known(v_____do__lift_530_, 1);
v___x_532_ = lean_apply_1(v_z_529_, v_val_531_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l_Option_elimM___redArg___lam__0___boxed(lean_object* v_y_533_, lean_object* v_z_534_, lean_object* v_____do__lift_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Option_elimM___redArg___lam__0(v_y_533_, v_z_534_, v_____do__lift_535_);
lean_dec(v_y_533_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Option_elimM___redArg(lean_object* v_inst_537_, lean_object* v_x_538_, lean_object* v_y_539_, lean_object* v_z_540_){
_start:
{
lean_object* v_toBind_541_; lean_object* v___f_542_; lean_object* v___x_543_; 
v_toBind_541_ = lean_ctor_get(v_inst_537_, 1);
lean_inc(v_toBind_541_);
lean_dec_ref(v_inst_537_);
v___f_542_ = lean_alloc_closure((void*)(l_Option_elimM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_542_, 0, v_y_539_);
lean_closure_set(v___f_542_, 1, v_z_540_);
v___x_543_ = lean_apply_4(v_toBind_541_, lean_box(0), lean_box(0), v_x_538_, v___f_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Option_elimM(lean_object* v_m_544_, lean_object* v_00_u03b1_545_, lean_object* v_00_u03b2_546_, lean_object* v_inst_547_, lean_object* v_x_548_, lean_object* v_y_549_, lean_object* v_z_550_){
_start:
{
lean_object* v_toBind_551_; lean_object* v___f_552_; lean_object* v___x_553_; 
v_toBind_551_ = lean_ctor_get(v_inst_547_, 1);
lean_inc(v_toBind_551_);
lean_dec_ref(v_inst_547_);
v___f_552_ = lean_alloc_closure((void*)(l_Option_elimM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_552_, 0, v_y_549_);
lean_closure_set(v___f_552_, 1, v_z_550_);
v___x_553_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v_x_548_, v___f_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Option_getDM___redArg(lean_object* v_inst_554_, lean_object* v_x_555_, lean_object* v_y_556_){
_start:
{
if (lean_obj_tag(v_x_555_) == 0)
{
lean_dec(v_inst_554_);
lean_inc(v_y_556_);
return v_y_556_;
}
else
{
lean_object* v_val_557_; lean_object* v___x_558_; 
v_val_557_ = lean_ctor_get(v_x_555_, 0);
lean_inc(v_val_557_);
lean_dec_ref_known(v_x_555_, 1);
v___x_558_ = lean_apply_2(v_inst_554_, lean_box(0), v_val_557_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_Option_getDM___redArg___boxed(lean_object* v_inst_559_, lean_object* v_x_560_, lean_object* v_y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Option_getDM___redArg(v_inst_559_, v_x_560_, v_y_561_);
lean_dec(v_y_561_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Option_getDM(lean_object* v_m_563_, lean_object* v_00_u03b1_564_, lean_object* v_inst_565_, lean_object* v_x_566_, lean_object* v_y_567_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_dec(v_inst_565_);
lean_inc(v_y_567_);
return v_y_567_;
}
else
{
lean_object* v_val_568_; lean_object* v___x_569_; 
v_val_568_ = lean_ctor_get(v_x_566_, 0);
lean_inc(v_val_568_);
lean_dec_ref_known(v_x_566_, 1);
v___x_569_ = lean_apply_2(v_inst_565_, lean_box(0), v_val_568_);
return v___x_569_;
}
}
}
LEAN_EXPORT lean_object* l_Option_getDM___boxed(lean_object* v_m_570_, lean_object* v_00_u03b1_571_, lean_object* v_inst_572_, lean_object* v_x_573_, lean_object* v_y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Option_getDM(v_m_570_, v_00_u03b1_571_, v_inst_572_, v_x_573_, v_y_574_);
lean_dec(v_y_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Option_min___redArg(lean_object* v_inst_576_, lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
lean_dec(v_inst_576_);
if (lean_obj_tag(v_x_578_) == 0)
{
return v_x_578_;
}
else
{
lean_dec_ref_known(v_x_578_, 1);
return v_x_577_;
}
}
else
{
if (lean_obj_tag(v_x_578_) == 0)
{
lean_dec_ref_known(v_x_577_, 1);
lean_dec(v_inst_576_);
return v_x_578_;
}
else
{
lean_object* v_val_579_; lean_object* v_val_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_588_; 
v_val_579_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_val_579_);
lean_dec_ref_known(v_x_577_, 1);
v_val_580_ = lean_ctor_get(v_x_578_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v_x_578_);
if (v_isSharedCheck_588_ == 0)
{
v___x_582_ = v_x_578_;
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_val_580_);
lean_dec(v_x_578_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_584_ = lean_apply_2(v_inst_576_, v_val_579_, v_val_580_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_584_);
v___x_586_ = v___x_582_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_min(lean_object* v_00_u03b1_589_, lean_object* v_inst_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Option_min___redArg(v_inst_590_, v_x_591_, v_x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Option_instMin___redArg(lean_object* v_inst_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_closure((void*)(l_Option_min), 4, 2);
lean_closure_set(v___x_595_, 0, lean_box(0));
lean_closure_set(v___x_595_, 1, v_inst_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Option_instMin(lean_object* v_00_u03b1_596_, lean_object* v_inst_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = lean_alloc_closure((void*)(l_Option_min), 4, 2);
lean_closure_set(v___x_598_, 0, lean_box(0));
lean_closure_set(v___x_598_, 1, v_inst_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Option_max___redArg(lean_object* v_inst_599_, lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
lean_dec(v_inst_599_);
return v_x_601_;
}
else
{
if (lean_obj_tag(v_x_601_) == 0)
{
lean_dec(v_inst_599_);
return v_x_600_;
}
else
{
lean_object* v_val_602_; lean_object* v_val_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_611_; 
v_val_602_ = lean_ctor_get(v_x_600_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v_x_600_, 1);
v_val_603_ = lean_ctor_get(v_x_601_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_x_601_);
if (v_isSharedCheck_611_ == 0)
{
v___x_605_ = v_x_601_;
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_val_603_);
lean_dec(v_x_601_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_607_ = lean_apply_2(v_inst_599_, v_val_602_, v_val_603_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_607_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_max(lean_object* v_00_u03b1_612_, lean_object* v_inst_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Option_max___redArg(v_inst_613_, v_x_614_, v_x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Option_instMax___redArg(lean_object* v_inst_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_closure((void*)(l_Option_max), 4, 2);
lean_closure_set(v___x_618_, 0, lean_box(0));
lean_closure_set(v___x_618_, 1, v_inst_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Option_instMax(lean_object* v_00_u03b1_619_, lean_object* v_inst_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_closure((void*)(l_Option_max), 4, 2);
lean_closure_set(v___x_621_, 0, lean_box(0));
lean_closure_set(v___x_621_, 1, v_inst_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_instLTOption___redArg(){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = lean_box(0);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_instLTOption___redArg___boxed(lean_object* v___dummy_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_instLTOption___redArg();
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_instLTOption(lean_object* v_00_u03b1_626_, lean_object* v_inst_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_box(0);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_instLEOption___redArg(){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_box(0);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_instLEOption___redArg___boxed(lean_object* v___dummy_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_instLEOption___redArg();
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_instLEOption(lean_object* v_00_u03b1_633_, lean_object* v_inst_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = lean_box(0);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_instFunctorOption___lam__0(lean_object* v_00_u03b1_636_, lean_object* v_00_u03b2_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
if (lean_obj_tag(v___y_639_) == 0)
{
lean_object* v___x_640_; 
lean_dec(v___y_638_);
v___x_640_ = lean_box(0);
return v___x_640_;
}
else
{
lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_isSharedCheck_647_ = !lean_is_exclusive(v___y_639_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v___y_639_, 0);
lean_dec(v_unused_648_);
v___x_642_ = v___y_639_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_dec(v___y_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___y_638_);
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___y_638_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__0(lean_object* v_00_u03b1_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_657_, 0, v___y_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__1(lean_object* v_00_u03b1_658_, lean_object* v_00_u03b2_659_, lean_object* v_f_660_, lean_object* v_x_661_){
_start:
{
if (lean_obj_tag(v_f_660_) == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v_x_661_);
v___x_662_ = lean_box(0);
return v___x_662_;
}
else
{
lean_object* v_val_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_val_663_ = lean_ctor_get(v_f_660_, 0);
lean_inc(v_val_663_);
lean_dec_ref_known(v_f_660_, 1);
v___x_664_ = lean_box(0);
v___x_665_ = lean_apply_1(v_x_661_, v___x_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_666_; 
lean_dec(v_val_663_);
v___x_666_ = lean_box(0);
return v___x_666_;
}
else
{
lean_object* v_val_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_675_; 
v_val_667_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_675_ == 0)
{
v___x_669_ = v___x_665_;
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_val_667_);
lean_dec(v___x_665_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = lean_apply_1(v_val_663_, v_val_667_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__2(lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_x_678_, lean_object* v_y_679_){
_start:
{
if (lean_obj_tag(v_x_678_) == 0)
{
lean_dec_ref(v_y_679_);
return v_x_678_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_box(0);
v___x_681_ = lean_apply_1(v_y_679_, v___x_680_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_682_; 
v___x_682_ = lean_box(0);
return v___x_682_;
}
else
{
lean_dec_ref_known(v___x_681_, 1);
lean_inc_ref(v_x_678_);
return v_x_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__2___boxed(lean_object* v_00_u03b1_683_, lean_object* v_00_u03b2_684_, lean_object* v_x_685_, lean_object* v_y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_instMonadOption___lam__2(v_00_u03b1_683_, v_00_u03b2_684_, v_x_685_, v_y_686_);
lean_dec(v_x_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__3(lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_x_690_, lean_object* v_y_691_){
_start:
{
if (lean_obj_tag(v_x_690_) == 0)
{
lean_object* v___x_692_; 
lean_dec_ref(v_y_691_);
v___x_692_ = lean_box(0);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_box(0);
v___x_694_ = lean_apply_1(v_y_691_, v___x_693_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadOption___lam__3___boxed(lean_object* v_00_u03b1_695_, lean_object* v_00_u03b2_696_, lean_object* v_x_697_, lean_object* v_y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_instMonadOption___lam__3(v_00_u03b1_695_, v_00_u03b2_696_, v_x_697_, v_y_698_);
lean_dec(v_x_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__0(lean_object* v_00_u03b1_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = lean_box(0);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__1(lean_object* v_00_u03b1_717_, lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
if (lean_obj_tag(v_x_718_) == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_box(0);
v___x_721_ = lean_apply_1(v_x_719_, v___x_720_);
return v___x_721_;
}
else
{
lean_dec_ref(v_x_719_);
lean_inc_ref(v_x_718_);
return v_x_718_;
}
}
}
LEAN_EXPORT lean_object* l_instAlternativeOption___lam__1___boxed(lean_object* v_00_u03b1_722_, lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_instAlternativeOption___lam__1(v_00_u03b1_722_, v_x_723_, v_x_724_);
lean_dec(v_x_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_liftOption___redArg(lean_object* v_inst_733_, lean_object* v_x_734_){
_start:
{
if (lean_obj_tag(v_x_734_) == 0)
{
lean_object* v_failure_735_; lean_object* v___x_736_; 
v_failure_735_ = lean_ctor_get(v_inst_733_, 1);
lean_inc(v_failure_735_);
lean_dec_ref(v_inst_733_);
v___x_736_ = lean_apply_1(v_failure_735_, lean_box(0));
return v___x_736_;
}
else
{
lean_object* v_toApplicative_737_; lean_object* v_toPure_738_; lean_object* v_val_739_; lean_object* v___x_740_; 
v_toApplicative_737_ = lean_ctor_get(v_inst_733_, 0);
lean_inc_ref(v_toApplicative_737_);
lean_dec_ref(v_inst_733_);
v_toPure_738_ = lean_ctor_get(v_toApplicative_737_, 1);
lean_inc(v_toPure_738_);
lean_dec_ref(v_toApplicative_737_);
v_val_739_ = lean_ctor_get(v_x_734_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v_x_734_, 1);
v___x_740_ = lean_apply_2(v_toPure_738_, lean_box(0), v_val_739_);
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l_liftOption(lean_object* v_m_741_, lean_object* v_00_u03b1_742_, lean_object* v_inst_743_, lean_object* v_x_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_liftOption___redArg(v_inst_743_, v_x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___redArg(lean_object* v_x_746_, lean_object* v_handle_747_){
_start:
{
if (lean_obj_tag(v_x_746_) == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_box(0);
v___x_749_ = lean_apply_1(v_handle_747_, v___x_748_);
return v___x_749_;
}
else
{
lean_dec_ref(v_handle_747_);
lean_inc_ref(v_x_746_);
return v_x_746_;
}
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___redArg___boxed(lean_object* v_x_750_, lean_object* v_handle_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Option_tryCatch___redArg(v_x_750_, v_handle_751_);
lean_dec(v_x_750_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch(lean_object* v_00_u03b1_753_, lean_object* v_x_754_, lean_object* v_handle_755_){
_start:
{
if (lean_obj_tag(v_x_754_) == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_box(0);
v___x_757_ = lean_apply_1(v_handle_755_, v___x_756_);
return v___x_757_;
}
else
{
lean_dec_ref(v_handle_755_);
lean_inc_ref(v_x_754_);
return v_x_754_;
}
}
}
LEAN_EXPORT lean_object* l_Option_tryCatch___boxed(lean_object* v_00_u03b1_758_, lean_object* v_x_759_, lean_object* v_handle_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Option_tryCatch(v_00_u03b1_758_, v_x_759_, v_handle_760_);
lean_dec(v_x_759_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfUnitOption___lam__0(lean_object* v_00_u03b1_762_, lean_object* v_x_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = lean_box(0);
return v___x_764_;
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
