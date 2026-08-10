// Lean compiler output
// Module: Lean.Util.ParamMinimizer
// Imports: public import Init.While public import Init.Data.Range.Polymorphic
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
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Util_ParamMinimizer_instInhabitedStatus_default;
LEAN_EXPORT uint8_t l_Lean_Util_ParamMinimizer_instInhabitedStatus;
static const lean_string_object l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Util.ParamMinimizer.Status.missing"};
static const lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__0 = (const lean_object*)&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__0_value;
static const lean_ctor_object l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__0_value)}};
static const lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1 = (const lean_object*)&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1_value;
static const lean_string_object l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Util.ParamMinimizer.Status.approx"};
static const lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__2 = (const lean_object*)&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__2_value;
static const lean_ctor_object l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__2_value)}};
static const lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3 = (const lean_object*)&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3_value;
static const lean_string_object l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Util.ParamMinimizer.Status.precise"};
static const lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__4 = (const lean_object*)&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__4_value;
static const lean_ctor_object l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__4_value)}};
static const lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5 = (const lean_object*)&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5_value;
static lean_once_cell_t l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6;
static lean_once_cell_t l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Util_ParamMinimizer_instReprStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Util_ParamMinimizer_instReprStatus_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Util_ParamMinimizer_instReprStatus___closed__0 = (const lean_object*)&l_Lean_Util_ParamMinimizer_instReprStatus___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Util_ParamMinimizer_instReprStatus = (const lean_object*)&l_Lean_Util_ParamMinimizer_instReprStatus___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0 = (const lean_object*)&l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Util_ParamMinimizer_Status_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Util_ParamMinimizer_Status_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg(lean_object* v_missing_23_){
_start:
{
lean_inc(v_missing_23_);
return v_missing_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg___boxed(lean_object* v_missing_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg(v_missing_24_);
lean_dec(v_missing_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_missing_29_){
_start:
{
lean_inc(v_missing_29_);
return v_missing_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_missing_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Util_ParamMinimizer_Status_missing_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_missing_33_);
lean_dec(v_missing_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg(lean_object* v_approx_36_){
_start:
{
lean_inc(v_approx_36_);
return v_approx_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg___boxed(lean_object* v_approx_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg(v_approx_37_);
lean_dec(v_approx_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_approx_42_){
_start:
{
lean_inc(v_approx_42_);
return v_approx_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_approx_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Util_ParamMinimizer_Status_approx_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_approx_46_);
lean_dec(v_approx_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg(lean_object* v_precise_49_){
_start:
{
lean_inc(v_precise_49_);
return v_precise_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg___boxed(lean_object* v_precise_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg(v_precise_50_);
lean_dec(v_precise_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_precise_55_){
_start:
{
lean_inc(v_precise_55_);
return v_precise_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_precise_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Util_ParamMinimizer_Status_precise_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_precise_59_);
lean_dec(v_precise_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
static lean_object* _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(2u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr(uint8_t v_x_77_, lean_object* v_prec_78_){
_start:
{
lean_object* v___y_80_; lean_object* v___y_87_; lean_object* v___y_94_; 
switch(v_x_77_)
{
case 0:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(1024u);
v___x_101_ = lean_nat_dec_le(v___x_100_, v_prec_78_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6);
v___y_80_ = v___x_102_;
goto v___jp_79_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7);
v___y_80_ = v___x_103_;
goto v___jp_79_;
}
}
case 1:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1024u);
v___x_105_ = lean_nat_dec_le(v___x_104_, v_prec_78_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6);
v___y_87_ = v___x_106_;
goto v___jp_86_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7);
v___y_87_ = v___x_107_;
goto v___jp_86_;
}
}
default: 
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(1024u);
v___x_109_ = lean_nat_dec_le(v___x_108_, v_prec_78_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6);
v___y_94_ = v___x_110_;
goto v___jp_93_;
}
else
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7);
v___y_94_ = v___x_111_;
goto v___jp_93_;
}
}
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_81_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1));
lean_inc(v___y_80_);
v___x_82_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_82_, 0, v___y_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = 0;
v___x_84_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_83_);
v___x_85_ = l_Repr_addAppParen(v___x_84_, v_prec_78_);
return v___x_85_;
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3));
lean_inc(v___y_87_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___y_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = l_Repr_addAppParen(v___x_91_, v_prec_78_);
return v___x_92_;
}
v___jp_93_:
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_95_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5));
lean_inc(v___y_94_);
v___x_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_96_, 0, v___y_94_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = 0;
v___x_98_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*1, v___x_97_);
v___x_99_ = l_Repr_addAppParen(v___x_98_, v_prec_78_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr___boxed(lean_object* v_x_112_, lean_object* v_prec_113_){
_start:
{
uint8_t v_x_177__boxed_114_; lean_object* v_res_115_; 
v_x_177__boxed_114_ = lean_unbox(v_x_112_);
v_res_115_ = l_Lean_Util_ParamMinimizer_instReprStatus_repr(v_x_177__boxed_114_, v_prec_113_);
lean_dec(v_prec_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0(lean_object* v_toPure_118_, lean_object* v_____x_119_){
_start:
{
lean_object* v_fst_120_; lean_object* v_snd_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_130_; 
v_fst_120_ = lean_ctor_get(v_____x_119_, 0);
v_snd_121_ = lean_ctor_get(v_____x_119_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_____x_119_);
if (v_isSharedCheck_130_ == 0)
{
v___x_123_ = v_____x_119_;
v_isShared_124_ = v_isSharedCheck_130_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_snd_121_);
lean_inc(v_fst_120_);
lean_dec(v_____x_119_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_130_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_125_, 0, v_fst_120_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_snd_121_);
v___x_127_ = v_reuseFailAlloc_129_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; 
v___x_128_ = lean_apply_2(v_toPure_118_, lean_box(0), v___x_127_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(lean_object* v_inst_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_toApplicative_133_; lean_object* v_toBind_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_157_; 
v_toApplicative_133_ = lean_ctor_get(v_inst_131_, 0);
v_toBind_134_ = lean_ctor_get(v_inst_131_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_inst_131_);
if (v_isSharedCheck_157_ == 0)
{
v___x_136_ = v_inst_131_;
v_isShared_137_ = v_isSharedCheck_157_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_toBind_134_);
lean_inc(v_toApplicative_133_);
lean_dec(v_inst_131_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_157_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_toPure_138_; lean_object* v_cur_139_; lean_object* v_added_140_; lean_object* v_numCalls_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_156_; 
v_toPure_138_ = lean_ctor_get(v_toApplicative_133_, 1);
lean_inc(v_toPure_138_);
lean_dec_ref(v_toApplicative_133_);
v_cur_139_ = lean_ctor_get(v_a_132_, 0);
v_added_140_ = lean_ctor_get(v_a_132_, 1);
v_numCalls_141_ = lean_ctor_get(v_a_132_, 2);
v_isSharedCheck_156_ = !lean_is_exclusive(v_a_132_);
if (v_isSharedCheck_156_ == 0)
{
v___x_143_ = v_a_132_;
v_isShared_144_ = v_isSharedCheck_156_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_numCalls_141_);
lean_inc(v_added_140_);
lean_inc(v_cur_139_);
lean_dec(v_a_132_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_156_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___f_145_; lean_object* v___x_146_; uint8_t v___x_147_; lean_object* v___x_149_; 
lean_inc(v_toPure_138_);
v___f_145_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_145_, 0, v_toPure_138_);
v___x_146_ = lean_box(0);
v___x_147_ = 1;
if (v_isShared_144_ == 0)
{
v___x_149_ = v___x_143_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_cur_139_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_added_140_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_numCalls_141_);
v___x_149_ = v_reuseFailAlloc_155_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_151_; 
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*3, v___x_147_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_149_);
lean_ctor_set(v___x_136_, 0, v___x_146_);
v___x_151_ = v___x_136_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___x_149_);
v___x_151_ = v_reuseFailAlloc_154_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_apply_2(v_toPure_138_, lean_box(0), v___x_151_);
v___x_153_ = lean_apply_4(v_toBind_134_, lean_box(0), lean_box(0), v___x_152_, v___f_145_);
return v___x_153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound(lean_object* v_m_158_, lean_object* v_inst_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(v_inst_159_, v_a_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___boxed(lean_object* v_m_163_, lean_object* v_inst_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound(v_m_163_, v_inst_164_, v_a_165_, v_a_166_);
lean_dec_ref(v_a_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___redArg(lean_object* v_inst_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_toApplicative_170_; lean_object* v_toBind_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_196_; 
v_toApplicative_170_ = lean_ctor_get(v_inst_168_, 0);
v_toBind_171_ = lean_ctor_get(v_inst_168_, 1);
v_isSharedCheck_196_ = !lean_is_exclusive(v_inst_168_);
if (v_isSharedCheck_196_ == 0)
{
v___x_173_ = v_inst_168_;
v_isShared_174_ = v_isSharedCheck_196_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_toBind_171_);
lean_inc(v_toApplicative_170_);
lean_dec(v_inst_168_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_196_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v_toPure_175_; lean_object* v_cur_176_; lean_object* v_added_177_; lean_object* v_numCalls_178_; uint8_t v_found_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_195_; 
v_toPure_175_ = lean_ctor_get(v_toApplicative_170_, 1);
lean_inc(v_toPure_175_);
lean_dec_ref(v_toApplicative_170_);
v_cur_176_ = lean_ctor_get(v_a_169_, 0);
v_added_177_ = lean_ctor_get(v_a_169_, 1);
v_numCalls_178_ = lean_ctor_get(v_a_169_, 2);
v_found_179_ = lean_ctor_get_uint8(v_a_169_, sizeof(void*)*3);
v_isSharedCheck_195_ = !lean_is_exclusive(v_a_169_);
if (v_isSharedCheck_195_ == 0)
{
v___x_181_ = v_a_169_;
v_isShared_182_ = v_isSharedCheck_195_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_numCalls_178_);
lean_inc(v_added_177_);
lean_inc(v_cur_176_);
lean_dec(v_a_169_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_195_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
lean_inc(v_toPure_175_);
v___f_183_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_183_, 0, v_toPure_175_);
v___x_184_ = lean_box(0);
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_add(v_numCalls_178_, v___x_185_);
lean_dec(v_numCalls_178_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 2, v___x_186_);
v___x_188_ = v___x_181_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_cur_176_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_added_177_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v___x_186_);
lean_ctor_set_uint8(v_reuseFailAlloc_194_, sizeof(void*)*3, v_found_179_);
v___x_188_ = v_reuseFailAlloc_194_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 1, v___x_188_);
lean_ctor_set(v___x_173_, 0, v___x_184_);
v___x_190_ = v___x_173_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___x_188_);
v___x_190_ = v_reuseFailAlloc_193_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_apply_2(v_toPure_175_, lean_box(0), v___x_190_);
v___x_192_ = lean_apply_4(v_toBind_171_, lean_box(0), lean_box(0), v___x_191_, v___f_183_);
return v___x_192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls(lean_object* v_m_197_, lean_object* v_inst_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___redArg(v_inst_198_, v_a_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___boxed(lean_object* v_m_202_, lean_object* v_inst_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls(v_m_202_, v_inst_203_, v_a_204_, v_a_205_);
lean_dec_ref(v_a_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(lean_object* v_i_207_, lean_object* v_inst_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_toApplicative_210_; lean_object* v_toBind_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_238_; 
v_toApplicative_210_ = lean_ctor_get(v_inst_208_, 0);
v_toBind_211_ = lean_ctor_get(v_inst_208_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_inst_208_);
if (v_isSharedCheck_238_ == 0)
{
v___x_213_ = v_inst_208_;
v_isShared_214_ = v_isSharedCheck_238_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_toBind_211_);
lean_inc(v_toApplicative_210_);
lean_dec(v_inst_208_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_238_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v_toPure_215_; lean_object* v_cur_216_; lean_object* v_added_217_; lean_object* v_numCalls_218_; uint8_t v_found_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_237_; 
v_toPure_215_ = lean_ctor_get(v_toApplicative_210_, 1);
lean_inc(v_toPure_215_);
lean_dec_ref(v_toApplicative_210_);
v_cur_216_ = lean_ctor_get(v_a_209_, 0);
v_added_217_ = lean_ctor_get(v_a_209_, 1);
v_numCalls_218_ = lean_ctor_get(v_a_209_, 2);
v_found_219_ = lean_ctor_get_uint8(v_a_209_, sizeof(void*)*3);
v_isSharedCheck_237_ = !lean_is_exclusive(v_a_209_);
if (v_isSharedCheck_237_ == 0)
{
v___x_221_ = v_a_209_;
v_isShared_222_ = v_isSharedCheck_237_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_numCalls_218_);
lean_inc(v_added_217_);
lean_inc(v_cur_216_);
lean_dec(v_a_209_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_237_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___f_223_; lean_object* v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
lean_inc(v_toPure_215_);
v___f_223_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_223_, 0, v_toPure_215_);
v___x_224_ = lean_box(0);
v___x_225_ = 1;
v___x_226_ = lean_box(v___x_225_);
v___x_227_ = lean_array_set(v_cur_216_, v_i_207_, v___x_226_);
v___x_228_ = lean_array_push(v_added_217_, v_i_207_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v___x_228_);
lean_ctor_set(v___x_221_, 0, v___x_227_);
v___x_230_ = v___x_221_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_numCalls_218_);
lean_ctor_set_uint8(v_reuseFailAlloc_236_, sizeof(void*)*3, v_found_219_);
v___x_230_ = v_reuseFailAlloc_236_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_232_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v___x_230_);
lean_ctor_set(v___x_213_, 0, v___x_224_);
v___x_232_ = v___x_213_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_230_);
v___x_232_ = v_reuseFailAlloc_235_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_apply_2(v_toPure_215_, lean_box(0), v___x_232_);
v___x_234_ = lean_apply_4(v_toBind_211_, lean_box(0), lean_box(0), v___x_233_, v___f_223_);
return v___x_234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add(lean_object* v_m_239_, lean_object* v_i_240_, lean_object* v_inst_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(v_i_240_, v_inst_241_, v_a_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___boxed(lean_object* v_m_245_, lean_object* v_i_246_, lean_object* v_inst_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add(v_m_245_, v_i_246_, v_inst_247_, v_a_248_, v_a_249_);
lean_dec_ref(v_a_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(lean_object* v_i_251_, lean_object* v_inst_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_toApplicative_254_; lean_object* v_toBind_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_281_; 
v_toApplicative_254_ = lean_ctor_get(v_inst_252_, 0);
v_toBind_255_ = lean_ctor_get(v_inst_252_, 1);
v_isSharedCheck_281_ = !lean_is_exclusive(v_inst_252_);
if (v_isSharedCheck_281_ == 0)
{
v___x_257_ = v_inst_252_;
v_isShared_258_ = v_isSharedCheck_281_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_toBind_255_);
lean_inc(v_toApplicative_254_);
lean_dec(v_inst_252_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_281_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v_toPure_259_; lean_object* v_cur_260_; lean_object* v_added_261_; lean_object* v_numCalls_262_; uint8_t v_found_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_280_; 
v_toPure_259_ = lean_ctor_get(v_toApplicative_254_, 1);
lean_inc(v_toPure_259_);
lean_dec_ref(v_toApplicative_254_);
v_cur_260_ = lean_ctor_get(v_a_253_, 0);
v_added_261_ = lean_ctor_get(v_a_253_, 1);
v_numCalls_262_ = lean_ctor_get(v_a_253_, 2);
v_found_263_ = lean_ctor_get_uint8(v_a_253_, sizeof(void*)*3);
v_isSharedCheck_280_ = !lean_is_exclusive(v_a_253_);
if (v_isSharedCheck_280_ == 0)
{
v___x_265_ = v_a_253_;
v_isShared_266_ = v_isSharedCheck_280_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_numCalls_262_);
lean_inc(v_added_261_);
lean_inc(v_cur_260_);
lean_dec(v_a_253_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_280_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___f_267_; lean_object* v___x_268_; uint8_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
lean_inc(v_toPure_259_);
v___f_267_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_267_, 0, v_toPure_259_);
v___x_268_ = lean_box(0);
v___x_269_ = 0;
v___x_270_ = lean_box(v___x_269_);
v___x_271_ = lean_array_set(v_cur_260_, v_i_251_, v___x_270_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_271_);
v___x_273_ = v___x_265_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_added_261_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_numCalls_262_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, sizeof(void*)*3, v_found_263_);
v___x_273_ = v_reuseFailAlloc_279_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_275_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v___x_273_);
lean_ctor_set(v___x_257_, 0, v___x_268_);
v___x_275_ = v___x_257_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_273_);
v___x_275_ = v_reuseFailAlloc_278_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_apply_2(v_toPure_259_, lean_box(0), v___x_275_);
v___x_277_ = lean_apply_4(v_toBind_255_, lean_box(0), lean_box(0), v___x_276_, v___f_267_);
return v___x_277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg___boxed(lean_object* v_i_282_, lean_object* v_inst_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v_i_282_, v_inst_283_, v_a_284_);
lean_dec(v_i_282_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase(lean_object* v_m_286_, lean_object* v_i_287_, lean_object* v_inst_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v_i_287_, v_inst_288_, v_a_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___boxed(lean_object* v_m_292_, lean_object* v_i_293_, lean_object* v_inst_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase(v_m_292_, v_i_293_, v_inst_294_, v_a_295_, v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_i_293_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(lean_object* v_i_298_, lean_object* v_inst_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_toApplicative_301_; lean_object* v_toBind_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_328_; 
v_toApplicative_301_ = lean_ctor_get(v_inst_299_, 0);
v_toBind_302_ = lean_ctor_get(v_inst_299_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_inst_299_);
if (v_isSharedCheck_328_ == 0)
{
v___x_304_ = v_inst_299_;
v_isShared_305_ = v_isSharedCheck_328_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_toBind_302_);
lean_inc(v_toApplicative_301_);
lean_dec(v_inst_299_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_328_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v_toPure_306_; lean_object* v_cur_307_; lean_object* v_added_308_; lean_object* v_numCalls_309_; uint8_t v_found_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_327_; 
v_toPure_306_ = lean_ctor_get(v_toApplicative_301_, 1);
lean_inc(v_toPure_306_);
lean_dec_ref(v_toApplicative_301_);
v_cur_307_ = lean_ctor_get(v_a_300_, 0);
v_added_308_ = lean_ctor_get(v_a_300_, 1);
v_numCalls_309_ = lean_ctor_get(v_a_300_, 2);
v_found_310_ = lean_ctor_get_uint8(v_a_300_, sizeof(void*)*3);
v_isSharedCheck_327_ = !lean_is_exclusive(v_a_300_);
if (v_isSharedCheck_327_ == 0)
{
v___x_312_ = v_a_300_;
v_isShared_313_ = v_isSharedCheck_327_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_numCalls_309_);
lean_inc(v_added_308_);
lean_inc(v_cur_307_);
lean_dec(v_a_300_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_327_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___f_314_; lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
lean_inc(v_toPure_306_);
v___f_314_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_314_, 0, v_toPure_306_);
v___x_315_ = lean_box(0);
v___x_316_ = 1;
v___x_317_ = lean_box(v___x_316_);
v___x_318_ = lean_array_set(v_cur_307_, v_i_298_, v___x_317_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_318_);
v___x_320_ = v___x_312_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_added_308_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_numCalls_309_);
lean_ctor_set_uint8(v_reuseFailAlloc_326_, sizeof(void*)*3, v_found_310_);
v___x_320_ = v_reuseFailAlloc_326_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_322_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v___x_320_);
lean_ctor_set(v___x_304_, 0, v___x_315_);
v___x_322_ = v___x_304_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_320_);
v___x_322_ = v_reuseFailAlloc_325_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_apply_2(v_toPure_306_, lean_box(0), v___x_322_);
v___x_324_ = lean_apply_4(v_toBind_302_, lean_box(0), lean_box(0), v___x_323_, v___f_314_);
return v___x_324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg___boxed(lean_object* v_i_329_, lean_object* v_inst_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v_i_329_, v_inst_330_, v_a_331_);
lean_dec(v_i_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore(lean_object* v_m_333_, lean_object* v_i_334_, lean_object* v_inst_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v_i_334_, v_inst_335_, v_a_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___boxed(lean_object* v_m_339_, lean_object* v_i_340_, lean_object* v_inst_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore(v_m_339_, v_i_340_, v_inst_341_, v_a_342_, v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_i_340_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(lean_object* v_toPure_345_, uint8_t v___x_346_, lean_object* v_____x_347_){
_start:
{
lean_object* v_fst_348_; 
v_fst_348_ = lean_ctor_get(v_____x_347_, 0);
lean_inc(v_fst_348_);
if (lean_obj_tag(v_fst_348_) == 0)
{
lean_object* v_snd_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_365_; 
v_snd_349_ = lean_ctor_get(v_____x_347_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v_____x_347_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v_____x_347_, 0);
lean_dec(v_unused_366_);
v___x_351_ = v_____x_347_;
v_isShared_352_ = v_isSharedCheck_365_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_snd_349_);
lean_dec(v_____x_347_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_365_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_364_; 
v_a_353_ = lean_ctor_get(v_fst_348_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v_fst_348_);
if (v_isSharedCheck_364_ == 0)
{
v___x_355_ = v_fst_348_;
v_isShared_356_ = v_isSharedCheck_364_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v_fst_348_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_364_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_363_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_360_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_358_);
v___x_360_ = v___x_351_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_snd_349_);
v___x_360_ = v_reuseFailAlloc_362_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; 
v___x_361_ = lean_apply_2(v_toPure_345_, lean_box(0), v___x_360_);
return v___x_361_;
}
}
}
}
}
else
{
lean_object* v_snd_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_384_; 
v_snd_367_ = lean_ctor_get(v_____x_347_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_____x_347_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v_____x_347_, 0);
lean_dec(v_unused_385_);
v___x_369_ = v_____x_347_;
v_isShared_370_ = v_isSharedCheck_384_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_snd_367_);
lean_dec(v_____x_347_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_384_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_382_; 
v_isSharedCheck_382_ = !lean_is_exclusive(v_fst_348_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v_fst_348_, 0);
lean_dec(v_unused_383_);
v___x_372_ = v_fst_348_;
v_isShared_373_ = v_isSharedCheck_382_;
goto v_resetjp_371_;
}
else
{
lean_dec(v_fst_348_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_382_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_box(v___x_346_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_381_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_376_);
v___x_378_ = v___x_369_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_snd_367_);
v___x_378_ = v_reuseFailAlloc_380_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; 
v___x_379_ = lean_apply_2(v_toPure_345_, lean_box(0), v___x_378_);
return v___x_379_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed(lean_object* v_toPure_386_, lean_object* v___x_387_, lean_object* v_____x_388_){
_start:
{
uint8_t v___x_7305__boxed_389_; lean_object* v_res_390_; 
v___x_7305__boxed_389_ = lean_unbox(v___x_387_);
v_res_390_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(v_toPure_386_, v___x_7305__boxed_389_, v_____x_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1(lean_object* v_toPure_391_, lean_object* v_inst_392_, lean_object* v_toBind_393_, lean_object* v___f_394_, lean_object* v_____x_395_){
_start:
{
lean_object* v_fst_396_; 
v_fst_396_ = lean_ctor_get(v_____x_395_, 0);
if (lean_obj_tag(v_fst_396_) == 0)
{
lean_object* v___x_397_; 
lean_dec(v___f_394_);
lean_dec(v_toBind_393_);
lean_dec_ref(v_inst_392_);
v___x_397_ = lean_apply_2(v_toPure_391_, lean_box(0), v_____x_395_);
return v___x_397_;
}
else
{
lean_object* v_a_398_; uint8_t v___x_399_; 
v_a_398_ = lean_ctor_get(v_fst_396_, 0);
v___x_399_ = lean_unbox(v_a_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; 
lean_dec(v___f_394_);
lean_dec(v_toBind_393_);
lean_dec_ref(v_inst_392_);
v___x_400_ = lean_apply_2(v_toPure_391_, lean_box(0), v_____x_395_);
return v___x_400_;
}
else
{
lean_object* v_snd_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec(v_toPure_391_);
v_snd_401_ = lean_ctor_get(v_____x_395_, 1);
lean_inc(v_snd_401_);
lean_dec_ref(v_____x_395_);
v___x_402_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(v_inst_392_, v_snd_401_);
v___x_403_ = lean_apply_4(v_toBind_393_, lean_box(0), lean_box(0), v___x_402_, v___f_394_);
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__2(lean_object* v_toPure_404_, lean_object* v_____x_405_){
_start:
{
lean_object* v_fst_406_; lean_object* v_snd_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_416_; 
v_fst_406_ = lean_ctor_get(v_____x_405_, 0);
v_snd_407_ = lean_ctor_get(v_____x_405_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v_____x_405_);
if (v_isSharedCheck_416_ == 0)
{
v___x_409_ = v_____x_405_;
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_snd_407_);
lean_inc(v_fst_406_);
lean_dec(v_____x_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v_fst_406_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_snd_407_);
v___x_413_ = v_reuseFailAlloc_415_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; 
v___x_414_ = lean_apply_2(v_toPure_404_, lean_box(0), v___x_413_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(lean_object* v_snd_417_, lean_object* v_toPure_418_, uint8_t v_a_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_box(v_a_419_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v_snd_417_);
v___x_422_ = lean_apply_2(v_toPure_418_, lean_box(0), v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3___boxed(lean_object* v_snd_423_, lean_object* v_toPure_424_, lean_object* v_a_425_){
_start:
{
uint8_t v_a_boxed_426_; lean_object* v_res_427_; 
v_a_boxed_426_ = lean_unbox(v_a_425_);
v_res_427_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(v_snd_423_, v_toPure_424_, v_a_boxed_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4(lean_object* v_toPure_428_, lean_object* v_a_429_, lean_object* v_toBind_430_, lean_object* v___f_431_, lean_object* v_____x_432_){
_start:
{
lean_object* v_fst_433_; 
v_fst_433_ = lean_ctor_get(v_____x_432_, 0);
lean_inc(v_fst_433_);
if (lean_obj_tag(v_fst_433_) == 0)
{
lean_object* v_snd_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_450_; 
lean_dec(v___f_431_);
lean_dec(v_toBind_430_);
lean_dec_ref(v_a_429_);
v_snd_434_ = lean_ctor_get(v_____x_432_, 1);
v_isSharedCheck_450_ = !lean_is_exclusive(v_____x_432_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; 
v_unused_451_ = lean_ctor_get(v_____x_432_, 0);
lean_dec(v_unused_451_);
v___x_436_ = v_____x_432_;
v_isShared_437_ = v_isSharedCheck_450_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_snd_434_);
lean_dec(v_____x_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_450_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_449_; 
v_a_438_ = lean_ctor_get(v_fst_433_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v_fst_433_);
if (v_isSharedCheck_449_ == 0)
{
v___x_440_ = v_fst_433_;
v_isShared_441_ = v_isSharedCheck_449_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v_fst_433_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_449_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_448_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_443_);
v___x_445_ = v___x_436_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_snd_434_);
v___x_445_ = v_reuseFailAlloc_447_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; 
v___x_446_ = lean_apply_2(v_toPure_428_, lean_box(0), v___x_445_);
return v___x_446_;
}
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v_snd_453_; lean_object* v_test_454_; lean_object* v_cur_455_; lean_object* v___x_456_; lean_object* v___f_457_; lean_object* v___f_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v_a_452_ = lean_ctor_get(v_fst_433_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v_fst_433_, 1);
v_snd_453_ = lean_ctor_get(v_____x_432_, 1);
lean_inc(v_snd_453_);
lean_dec_ref(v_____x_432_);
v_test_454_ = lean_ctor_get(v_a_429_, 1);
lean_inc(v_test_454_);
lean_dec_ref(v_a_429_);
v_cur_455_ = lean_ctor_get(v_a_452_, 0);
lean_inc_ref(v_cur_455_);
lean_dec(v_a_452_);
v___x_456_ = lean_apply_1(v_test_454_, v_cur_455_);
lean_inc(v_toPure_428_);
v___f_457_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__2), 2, 1);
lean_closure_set(v___f_457_, 0, v_toPure_428_);
v___f_458_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_458_, 0, v_snd_453_);
lean_closure_set(v___f_458_, 1, v_toPure_428_);
lean_inc_n(v_toBind_430_, 2);
v___x_459_ = lean_apply_4(v_toBind_430_, lean_box(0), lean_box(0), v___x_456_, v___f_458_);
v___x_460_ = lean_apply_4(v_toBind_430_, lean_box(0), lean_box(0), v___x_459_, v___f_457_);
v___x_461_ = lean_apply_4(v_toBind_430_, lean_box(0), lean_box(0), v___x_460_, v___f_431_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5(lean_object* v_toPure_462_, lean_object* v_____x_463_){
_start:
{
lean_object* v_fst_464_; lean_object* v_snd_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_474_; 
v_fst_464_ = lean_ctor_get(v_____x_463_, 0);
v_snd_465_ = lean_ctor_get(v_____x_463_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_____x_463_);
if (v_isSharedCheck_474_ == 0)
{
v___x_467_ = v_____x_463_;
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_snd_465_);
lean_inc(v_fst_464_);
lean_dec(v_____x_463_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v_fst_464_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_469_);
v___x_471_ = v___x_467_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_snd_465_);
v___x_471_ = v_reuseFailAlloc_473_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; 
v___x_472_ = lean_apply_2(v_toPure_462_, lean_box(0), v___x_471_);
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6(lean_object* v_toPure_475_, lean_object* v_toBind_476_, lean_object* v___f_477_, lean_object* v_____x_478_){
_start:
{
lean_object* v_fst_479_; 
v_fst_479_ = lean_ctor_get(v_____x_478_, 0);
lean_inc(v_fst_479_);
if (lean_obj_tag(v_fst_479_) == 0)
{
lean_object* v_snd_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_496_; 
lean_dec(v___f_477_);
lean_dec(v_toBind_476_);
v_snd_480_ = lean_ctor_get(v_____x_478_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_____x_478_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v_____x_478_, 0);
lean_dec(v_unused_497_);
v___x_482_ = v_____x_478_;
v_isShared_483_ = v_isSharedCheck_496_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_snd_480_);
lean_dec(v_____x_478_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_496_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_495_; 
v_a_484_ = lean_ctor_get(v_fst_479_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_fst_479_);
if (v_isSharedCheck_495_ == 0)
{
v___x_486_ = v_fst_479_;
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v_fst_479_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_494_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_489_);
v___x_491_ = v___x_482_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_snd_480_);
v___x_491_ = v_reuseFailAlloc_493_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; 
v___x_492_ = lean_apply_2(v_toPure_475_, lean_box(0), v___x_491_);
return v___x_492_;
}
}
}
}
}
else
{
lean_object* v_snd_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_511_; 
v_snd_498_ = lean_ctor_get(v_____x_478_, 1);
v_isSharedCheck_511_ = !lean_is_exclusive(v_____x_478_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; 
v_unused_512_ = lean_ctor_get(v_____x_478_, 0);
lean_dec(v_unused_512_);
v___x_500_ = v_____x_478_;
v_isShared_501_ = v_isSharedCheck_511_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snd_498_);
lean_dec(v_____x_478_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_511_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v_a_502_; lean_object* v___f_503_; lean_object* v___f_504_; lean_object* v___x_506_; 
v_a_502_ = lean_ctor_get(v_fst_479_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v_fst_479_, 1);
lean_inc(v_toBind_476_);
lean_inc_n(v_toPure_475_, 2);
v___f_503_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4), 5, 4);
lean_closure_set(v___f_503_, 0, v_toPure_475_);
lean_closure_set(v___f_503_, 1, v_a_502_);
lean_closure_set(v___f_503_, 2, v_toBind_476_);
lean_closure_set(v___f_503_, 3, v___f_477_);
v___f_504_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_504_, 0, v_toPure_475_);
lean_inc(v_snd_498_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v_snd_498_);
v___x_506_ = v___x_500_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_snd_498_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_snd_498_);
v___x_506_ = v_reuseFailAlloc_510_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_apply_2(v_toPure_475_, lean_box(0), v___x_506_);
lean_inc(v_toBind_476_);
v___x_508_ = lean_apply_4(v_toBind_476_, lean_box(0), lean_box(0), v___x_507_, v___f_504_);
v___x_509_ = lean_apply_4(v_toBind_476_, lean_box(0), lean_box(0), v___x_508_, v___f_503_);
return v___x_509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7(lean_object* v_toPure_513_, lean_object* v_a_514_, lean_object* v_toBind_515_, lean_object* v___f_516_, lean_object* v_____x_517_){
_start:
{
lean_object* v_fst_518_; 
v_fst_518_ = lean_ctor_get(v_____x_517_, 0);
lean_inc(v_fst_518_);
if (lean_obj_tag(v_fst_518_) == 0)
{
lean_object* v_snd_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_535_; 
lean_dec(v___f_516_);
lean_dec(v_toBind_515_);
v_snd_519_ = lean_ctor_get(v_____x_517_, 1);
v_isSharedCheck_535_ = !lean_is_exclusive(v_____x_517_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; 
v_unused_536_ = lean_ctor_get(v_____x_517_, 0);
lean_dec(v_unused_536_);
v___x_521_ = v_____x_517_;
v_isShared_522_ = v_isSharedCheck_535_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_snd_519_);
lean_dec(v_____x_517_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_535_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_534_; 
v_a_523_ = lean_ctor_get(v_fst_518_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_fst_518_);
if (v_isSharedCheck_534_ == 0)
{
v___x_525_ = v_fst_518_;
v_isShared_526_ = v_isSharedCheck_534_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v_fst_518_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_534_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_533_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_528_);
v___x_530_ = v___x_521_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_snd_519_);
v___x_530_ = v_reuseFailAlloc_532_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; 
v___x_531_ = lean_apply_2(v_toPure_513_, lean_box(0), v___x_530_);
return v___x_531_;
}
}
}
}
}
else
{
lean_object* v_snd_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_554_; 
v_snd_537_ = lean_ctor_get(v_____x_517_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_____x_517_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v_____x_517_, 0);
lean_dec(v_unused_555_);
v___x_539_ = v_____x_517_;
v_isShared_540_ = v_isSharedCheck_554_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_snd_537_);
lean_dec(v_____x_517_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_554_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_552_; 
v_isSharedCheck_552_ = !lean_is_exclusive(v_fst_518_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v_fst_518_, 0);
lean_dec(v_unused_553_);
v___x_542_ = v_fst_518_;
v_isShared_543_ = v_isSharedCheck_552_;
goto v_resetjp_541_;
}
else
{
lean_dec(v_fst_518_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_552_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
lean_inc_ref(v_a_514_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v_a_514_);
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_514_);
v___x_545_ = v_reuseFailAlloc_551_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_547_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_545_);
v___x_547_ = v___x_539_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_snd_537_);
v___x_547_ = v_reuseFailAlloc_550_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_apply_2(v_toPure_513_, lean_box(0), v___x_547_);
v___x_549_ = lean_apply_4(v_toBind_515_, lean_box(0), lean_box(0), v___x_548_, v___f_516_);
return v___x_549_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7___boxed(lean_object* v_toPure_556_, lean_object* v_a_557_, lean_object* v_toBind_558_, lean_object* v___f_559_, lean_object* v_____x_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7(v_toPure_556_, v_a_557_, v_toBind_558_, v___f_559_, v_____x_560_);
lean_dec_ref(v_a_557_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(lean_object* v_toPure_564_, lean_object* v_inst_565_, lean_object* v_toBind_566_, lean_object* v_a_567_, lean_object* v_maxCalls_568_, lean_object* v_____x_569_){
_start:
{
lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_624_; 
v_fst_570_ = lean_ctor_get(v_____x_569_, 0);
v_snd_571_ = lean_ctor_get(v_____x_569_, 1);
v_isSharedCheck_624_ = !lean_is_exclusive(v_____x_569_);
if (v_isSharedCheck_624_ == 0)
{
v___x_573_ = v_____x_569_;
v_isShared_574_ = v_isSharedCheck_624_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_snd_571_);
lean_inc(v_fst_570_);
lean_dec(v_____x_569_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_624_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
uint8_t v___y_576_; 
if (lean_obj_tag(v_fst_570_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_618_; 
lean_del_object(v___x_573_);
lean_dec(v_toBind_566_);
lean_dec_ref(v_inst_565_);
v_a_609_ = lean_ctor_get(v_fst_570_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v_fst_570_);
if (v_isSharedCheck_618_ == 0)
{
v___x_611_ = v_fst_570_;
v_isShared_612_ = v_isSharedCheck_618_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v_fst_570_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_618_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_617_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v_snd_571_);
v___x_616_ = lean_apply_2(v_toPure_564_, lean_box(0), v___x_615_);
return v___x_616_;
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_a_619_ = lean_ctor_get(v_fst_570_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v_fst_570_, 1);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_nat_dec_lt(v___x_620_, v_maxCalls_568_);
if (v___x_621_ == 0)
{
lean_dec(v_a_619_);
v___y_576_ = v___x_621_;
goto v___jp_575_;
}
else
{
lean_object* v_numCalls_622_; uint8_t v___x_623_; 
v_numCalls_622_ = lean_ctor_get(v_a_619_, 2);
lean_inc(v_numCalls_622_);
lean_dec(v_a_619_);
v___x_623_ = lean_nat_dec_le(v_maxCalls_568_, v_numCalls_622_);
lean_dec(v_numCalls_622_);
v___y_576_ = v___x_623_;
goto v___jp_575_;
}
}
v___jp_575_:
{
if (v___y_576_ == 0)
{
lean_object* v_cur_577_; lean_object* v_added_578_; lean_object* v_numCalls_579_; uint8_t v_found_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_603_; 
v_cur_577_ = lean_ctor_get(v_snd_571_, 0);
v_added_578_ = lean_ctor_get(v_snd_571_, 1);
v_numCalls_579_ = lean_ctor_get(v_snd_571_, 2);
v_found_580_ = lean_ctor_get_uint8(v_snd_571_, sizeof(void*)*3);
v_isSharedCheck_603_ = !lean_is_exclusive(v_snd_571_);
if (v_isSharedCheck_603_ == 0)
{
v___x_582_ = v_snd_571_;
v_isShared_583_ = v_isSharedCheck_603_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_numCalls_579_);
lean_inc(v_added_578_);
lean_inc(v_cur_577_);
lean_dec(v_snd_571_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_603_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
uint8_t v___x_584_; lean_object* v___x_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_584_ = 1;
v___x_585_ = lean_box(v___x_584_);
lean_inc_n(v_toPure_564_, 5);
v___f_586_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_586_, 0, v_toPure_564_);
lean_closure_set(v___f_586_, 1, v___x_585_);
lean_inc_n(v_toBind_566_, 3);
v___f_587_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1), 5, 4);
lean_closure_set(v___f_587_, 0, v_toPure_564_);
lean_closure_set(v___f_587_, 1, v_inst_565_);
lean_closure_set(v___f_587_, 2, v_toBind_566_);
lean_closure_set(v___f_587_, 3, v___f_586_);
v___f_588_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6), 4, 3);
lean_closure_set(v___f_588_, 0, v_toPure_564_);
lean_closure_set(v___f_588_, 1, v_toBind_566_);
lean_closure_set(v___f_588_, 2, v___f_587_);
lean_inc_ref(v_a_567_);
v___f_589_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7___boxed), 5, 4);
lean_closure_set(v___f_589_, 0, v_toPure_564_);
lean_closure_set(v___f_589_, 1, v_a_567_);
lean_closure_set(v___f_589_, 2, v_toBind_566_);
lean_closure_set(v___f_589_, 3, v___f_588_);
v___f_590_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_590_, 0, v_toPure_564_);
v___x_591_ = lean_box(0);
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_nat_add(v_numCalls_579_, v___x_592_);
lean_dec(v_numCalls_579_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 2, v___x_593_);
v___x_595_ = v___x_582_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_cur_577_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_added_578_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v___x_593_);
lean_ctor_set_uint8(v_reuseFailAlloc_602_, sizeof(void*)*3, v_found_580_);
v___x_595_ = v_reuseFailAlloc_602_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_597_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v___x_595_);
lean_ctor_set(v___x_573_, 0, v___x_591_);
v___x_597_ = v___x_573_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v___x_595_);
v___x_597_ = v_reuseFailAlloc_601_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_apply_2(v_toPure_564_, lean_box(0), v___x_597_);
lean_inc(v_toBind_566_);
v___x_599_ = lean_apply_4(v_toBind_566_, lean_box(0), lean_box(0), v___x_598_, v___f_590_);
v___x_600_ = lean_apply_4(v_toBind_566_, lean_box(0), lean_box(0), v___x_599_, v___f_589_);
return v___x_600_;
}
}
}
}
else
{
lean_object* v___x_604_; lean_object* v___x_606_; 
lean_dec(v_toBind_566_);
lean_dec_ref(v_inst_565_);
v___x_604_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0));
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_604_);
v___x_606_ = v___x_573_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_snd_571_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; 
v___x_607_ = lean_apply_2(v_toPure_564_, lean_box(0), v___x_606_);
return v___x_607_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed(lean_object* v_toPure_625_, lean_object* v_inst_626_, lean_object* v_toBind_627_, lean_object* v_a_628_, lean_object* v_maxCalls_629_, lean_object* v_____x_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(v_toPure_625_, v_inst_626_, v_toBind_627_, v_a_628_, v_maxCalls_629_, v_____x_630_);
lean_dec(v_maxCalls_629_);
lean_dec_ref(v_a_628_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(lean_object* v_toPure_632_, lean_object* v_inst_633_, lean_object* v_toBind_634_, lean_object* v_a_635_, lean_object* v_____x_636_){
_start:
{
lean_object* v_fst_637_; 
v_fst_637_ = lean_ctor_get(v_____x_636_, 0);
lean_inc(v_fst_637_);
if (lean_obj_tag(v_fst_637_) == 0)
{
lean_object* v_snd_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_toBind_634_);
lean_dec_ref(v_inst_633_);
v_snd_638_ = lean_ctor_get(v_____x_636_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_____x_636_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v_____x_636_, 0);
lean_dec(v_unused_655_);
v___x_640_ = v_____x_636_;
v_isShared_641_ = v_isSharedCheck_654_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_snd_638_);
lean_dec(v_____x_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_654_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_653_; 
v_a_642_ = lean_ctor_get(v_fst_637_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_fst_637_);
if (v_isSharedCheck_653_ == 0)
{
v___x_644_ = v_fst_637_;
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v_fst_637_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_652_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_647_);
v___x_649_ = v___x_640_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_snd_638_);
v___x_649_ = v_reuseFailAlloc_651_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; 
v___x_650_ = lean_apply_2(v_toPure_632_, lean_box(0), v___x_649_);
return v___x_650_;
}
}
}
}
}
else
{
lean_object* v_a_656_; lean_object* v_snd_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_670_; 
v_a_656_ = lean_ctor_get(v_fst_637_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v_fst_637_, 1);
v_snd_657_ = lean_ctor_get(v_____x_636_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_____x_636_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v_____x_636_, 0);
lean_dec(v_unused_671_);
v___x_659_ = v_____x_636_;
v_isShared_660_ = v_isSharedCheck_670_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snd_657_);
lean_dec(v_____x_636_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_670_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_maxCalls_661_; lean_object* v___f_662_; lean_object* v___f_663_; lean_object* v___x_665_; 
v_maxCalls_661_ = lean_ctor_get(v_a_656_, 2);
lean_inc(v_maxCalls_661_);
lean_dec(v_a_656_);
lean_inc_ref(v_a_635_);
lean_inc(v_toBind_634_);
lean_inc_n(v_toPure_632_, 2);
v___f_662_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_662_, 0, v_toPure_632_);
lean_closure_set(v___f_662_, 1, v_inst_633_);
lean_closure_set(v___f_662_, 2, v_toBind_634_);
lean_closure_set(v___f_662_, 3, v_a_635_);
lean_closure_set(v___f_662_, 4, v_maxCalls_661_);
v___f_663_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_663_, 0, v_toPure_632_);
lean_inc(v_snd_657_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_snd_657_);
v___x_665_ = v___x_659_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_snd_657_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_snd_657_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_apply_2(v_toPure_632_, lean_box(0), v___x_665_);
lean_inc(v_toBind_634_);
v___x_667_ = lean_apply_4(v_toBind_634_, lean_box(0), lean_box(0), v___x_666_, v___f_663_);
v___x_668_ = lean_apply_4(v_toBind_634_, lean_box(0), lean_box(0), v___x_667_, v___f_662_);
return v___x_668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed(lean_object* v_toPure_672_, lean_object* v_inst_673_, lean_object* v_toBind_674_, lean_object* v_a_675_, lean_object* v_____x_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(v_toPure_672_, v_inst_673_, v_toBind_674_, v_a_675_, v_____x_676_);
lean_dec_ref(v_a_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(lean_object* v_inst_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_toApplicative_681_; lean_object* v_toBind_682_; lean_object* v_toPure_683_; lean_object* v___f_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_toApplicative_681_ = lean_ctor_get(v_inst_678_, 0);
v_toBind_682_ = lean_ctor_get(v_inst_678_, 1);
lean_inc_n(v_toBind_682_, 2);
v_toPure_683_ = lean_ctor_get(v_toApplicative_681_, 1);
lean_inc_n(v_toPure_683_, 2);
lean_inc_ref_n(v_a_679_, 2);
v___f_684_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_684_, 0, v_toPure_683_);
lean_closure_set(v___f_684_, 1, v_inst_678_);
lean_closure_set(v___f_684_, 2, v_toBind_682_);
lean_closure_set(v___f_684_, 3, v_a_679_);
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v_a_679_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v_a_680_);
v___x_687_ = lean_apply_2(v_toPure_683_, lean_box(0), v___x_686_);
v___x_688_ = lean_apply_4(v_toBind_682_, lean_box(0), lean_box(0), v___x_687_, v___f_684_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___boxed(lean_object* v_inst_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_689_, v_a_690_, v_a_691_);
lean_dec_ref(v_a_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(lean_object* v_m_693_, lean_object* v_inst_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_694_, v_a_695_, v_a_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___boxed(lean_object* v_m_698_, lean_object* v_inst_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(v_m_698_, v_inst_699_, v_a_700_, v_a_701_);
lean_dec_ref(v_a_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0(lean_object* v_toPure_703_, lean_object* v_____x_704_){
_start:
{
lean_object* v_fst_705_; 
v_fst_705_ = lean_ctor_get(v_____x_704_, 0);
lean_inc(v_fst_705_);
if (lean_obj_tag(v_fst_705_) == 0)
{
lean_object* v_snd_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_722_; 
v_snd_706_ = lean_ctor_get(v_____x_704_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_____x_704_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v_____x_704_, 0);
lean_dec(v_unused_723_);
v___x_708_ = v_____x_704_;
v_isShared_709_ = v_isSharedCheck_722_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_snd_706_);
lean_dec(v_____x_704_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_722_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_721_; 
v_a_710_ = lean_ctor_get(v_fst_705_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v_fst_705_);
if (v_isSharedCheck_721_ == 0)
{
v___x_712_ = v_fst_705_;
v_isShared_713_ = v_isSharedCheck_721_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v_fst_705_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_721_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_720_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_715_);
v___x_717_ = v___x_708_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_snd_706_);
v___x_717_ = v_reuseFailAlloc_719_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; 
v___x_718_ = lean_apply_2(v_toPure_703_, lean_box(0), v___x_717_);
return v___x_718_;
}
}
}
}
}
else
{
lean_object* v_snd_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_740_; 
v_snd_724_ = lean_ctor_get(v_____x_704_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_____x_704_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v_____x_704_, 0);
lean_dec(v_unused_741_);
v___x_726_ = v_____x_704_;
v_isShared_727_ = v_isSharedCheck_740_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_snd_724_);
lean_dec(v_____x_704_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_740_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_739_; 
v_a_728_ = lean_ctor_get(v_fst_705_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_fst_705_);
if (v_isSharedCheck_739_ == 0)
{
v___x_730_ = v_fst_705_;
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v_fst_705_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_738_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_733_);
v___x_735_ = v___x_726_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_snd_724_);
v___x_735_ = v_reuseFailAlloc_737_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_736_; 
v___x_736_ = lean_apply_2(v_toPure_703_, lean_box(0), v___x_735_);
return v___x_736_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1(lean_object* v_toPure_742_, lean_object* v___x_743_, lean_object* v_____x_744_){
_start:
{
lean_object* v_fst_745_; 
v_fst_745_ = lean_ctor_get(v_____x_744_, 0);
lean_inc(v_fst_745_);
if (lean_obj_tag(v_fst_745_) == 0)
{
lean_object* v_snd_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_762_; 
v_snd_746_ = lean_ctor_get(v_____x_744_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v_____x_744_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v_____x_744_, 0);
lean_dec(v_unused_763_);
v___x_748_ = v_____x_744_;
v_isShared_749_ = v_isSharedCheck_762_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_snd_746_);
lean_dec(v_____x_744_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_762_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_761_; 
v_a_750_ = lean_ctor_get(v_fst_745_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_fst_745_);
if (v_isSharedCheck_761_ == 0)
{
v___x_752_ = v_fst_745_;
v_isShared_753_ = v_isSharedCheck_761_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v_fst_745_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_761_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_760_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_757_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_755_);
v___x_757_ = v___x_748_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_snd_746_);
v___x_757_ = v_reuseFailAlloc_759_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; 
v___x_758_ = lean_apply_2(v_toPure_742_, lean_box(0), v___x_757_);
return v___x_758_;
}
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_791_; 
v_a_764_ = lean_ctor_get(v_fst_745_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v_fst_745_);
if (v_isSharedCheck_791_ == 0)
{
v___x_766_ = v_fst_745_;
v_isShared_767_ = v_isSharedCheck_791_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v_fst_745_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_791_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v_fst_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_789_; 
v_fst_768_ = lean_ctor_get(v_a_764_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v_a_764_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v_a_764_, 1);
lean_dec(v_unused_790_);
v___x_770_ = v_a_764_;
v_isShared_771_ = v_isSharedCheck_789_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_fst_768_);
lean_dec(v_a_764_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_789_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
if (lean_obj_tag(v_fst_768_) == 0)
{
lean_object* v_snd_772_; lean_object* v___x_774_; 
v_snd_772_ = lean_ctor_get(v_____x_744_, 1);
lean_inc(v_snd_772_);
lean_dec_ref(v_____x_744_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_743_);
v___x_774_ = v___x_766_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_743_);
v___x_774_ = v_reuseFailAlloc_779_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v_snd_772_);
lean_ctor_set(v___x_770_, 0, v___x_774_);
v___x_776_ = v___x_770_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_snd_772_);
v___x_776_ = v_reuseFailAlloc_778_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; 
v___x_777_ = lean_apply_2(v_toPure_742_, lean_box(0), v___x_776_);
return v___x_777_;
}
}
}
else
{
lean_object* v_snd_780_; lean_object* v_val_781_; lean_object* v___x_783_; 
v_snd_780_ = lean_ctor_get(v_____x_744_, 1);
lean_inc(v_snd_780_);
lean_dec_ref(v_____x_744_);
v_val_781_ = lean_ctor_get(v_fst_768_, 0);
lean_inc(v_val_781_);
lean_dec_ref_known(v_fst_768_, 1);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v_val_781_);
v___x_783_ = v___x_766_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_val_781_);
v___x_783_ = v_reuseFailAlloc_788_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_785_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v_snd_780_);
lean_ctor_set(v___x_770_, 0, v___x_783_);
v___x_785_ = v___x_770_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_snd_780_);
v___x_785_ = v_reuseFailAlloc_787_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; 
v___x_786_ = lean_apply_2(v_toPure_742_, lean_box(0), v___x_785_);
return v___x_786_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2(lean_object* v_toPure_792_, lean_object* v___x_793_, lean_object* v___x_794_, lean_object* v_____x_795_){
_start:
{
lean_object* v_fst_796_; 
v_fst_796_ = lean_ctor_get(v_____x_795_, 0);
lean_inc(v_fst_796_);
if (lean_obj_tag(v_fst_796_) == 0)
{
lean_object* v_snd_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref(v___x_793_);
v_snd_797_ = lean_ctor_get(v_____x_795_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_____x_795_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v_____x_795_, 0);
lean_dec(v_unused_814_);
v___x_799_ = v_____x_795_;
v_isShared_800_ = v_isSharedCheck_813_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_snd_797_);
lean_dec(v_____x_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_813_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_812_; 
v_a_801_ = lean_ctor_get(v_fst_796_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v_fst_796_);
if (v_isSharedCheck_812_ == 0)
{
v___x_803_ = v_fst_796_;
v_isShared_804_ = v_isSharedCheck_812_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v_fst_796_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_812_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_811_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_806_);
v___x_808_ = v___x_799_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_snd_797_);
v___x_808_ = v_reuseFailAlloc_810_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; 
v___x_809_ = lean_apply_2(v_toPure_792_, lean_box(0), v___x_808_);
return v___x_809_;
}
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_850_; 
v_a_815_ = lean_ctor_get(v_fst_796_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v_fst_796_);
if (v_isSharedCheck_850_ == 0)
{
v___x_817_ = v_fst_796_;
v_isShared_818_ = v_isSharedCheck_850_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v_fst_796_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_850_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
uint8_t v___x_819_; 
v___x_819_ = lean_unbox(v_a_815_);
lean_dec(v_a_815_);
if (v___x_819_ == 0)
{
lean_object* v_snd_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_832_; 
v_snd_820_ = lean_ctor_get(v_____x_795_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_____x_795_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v_____x_795_, 0);
lean_dec(v_unused_833_);
v___x_822_ = v_____x_795_;
v_isShared_823_ = v_isSharedCheck_832_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_snd_820_);
lean_dec(v_____x_795_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_832_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_793_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_824_);
v___x_826_ = v___x_817_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_831_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_828_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_826_);
v___x_828_ = v___x_822_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_snd_820_);
v___x_828_ = v_reuseFailAlloc_830_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; 
v___x_829_ = lean_apply_2(v_toPure_792_, lean_box(0), v___x_828_);
return v___x_829_;
}
}
}
}
else
{
lean_object* v_snd_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_848_; 
lean_dec_ref(v___x_793_);
v_snd_834_ = lean_ctor_get(v_____x_795_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_____x_795_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v_____x_795_, 0);
lean_dec(v_unused_849_);
v___x_836_ = v_____x_795_;
v_isShared_837_ = v_isSharedCheck_848_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_snd_834_);
lean_dec(v_____x_795_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_848_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_794_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_794_);
lean_ctor_set(v___x_836_, 0, v___x_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_794_);
v___x_840_ = v_reuseFailAlloc_847_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_841_);
v___x_843_ = v___x_817_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_846_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v_snd_834_);
v___x_845_ = lean_apply_2(v_toPure_792_, lean_box(0), v___x_844_);
return v___x_845_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(lean_object* v_inst_851_, lean_object* v_toBind_852_, lean_object* v___f_853_, lean_object* v_____r_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_851_, v___y_855_, v___y_856_);
v___x_858_ = lean_apply_4(v_toBind_852_, lean_box(0), lean_box(0), v___x_857_, v___f_853_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed(lean_object* v_inst_859_, lean_object* v_toBind_860_, lean_object* v___f_861_, lean_object* v_____r_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(v_inst_859_, v_toBind_860_, v___f_861_, v_____r_862_, v___y_863_, v___y_864_);
lean_dec_ref(v___y_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(lean_object* v_toPure_866_, lean_object* v_next_867_, lean_object* v_G_868_, lean_object* v___y_869_, lean_object* v_____x_870_){
_start:
{
lean_object* v_fst_871_; 
v_fst_871_ = lean_ctor_get(v_____x_870_, 0);
lean_inc(v_fst_871_);
if (lean_obj_tag(v_fst_871_) == 0)
{
lean_object* v_snd_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_G_868_);
v_snd_872_ = lean_ctor_get(v_____x_870_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_____x_870_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v_____x_870_, 0);
lean_dec(v_unused_889_);
v___x_874_ = v_____x_870_;
v_isShared_875_ = v_isSharedCheck_888_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_snd_872_);
lean_dec(v_____x_870_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_888_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_887_; 
v_a_876_ = lean_ctor_get(v_fst_871_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v_fst_871_);
if (v_isSharedCheck_887_ == 0)
{
v___x_878_ = v_fst_871_;
v_isShared_879_ = v_isSharedCheck_887_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v_fst_871_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_887_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_886_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_881_);
v___x_883_ = v___x_874_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_snd_872_);
v___x_883_ = v_reuseFailAlloc_885_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; 
v___x_884_ = lean_apply_2(v_toPure_866_, lean_box(0), v___x_883_);
return v___x_884_;
}
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_913_; 
v_a_890_ = lean_ctor_get(v_fst_871_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v_fst_871_);
if (v_isSharedCheck_913_ == 0)
{
v___x_892_ = v_fst_871_;
v_isShared_893_ = v_isSharedCheck_913_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v_fst_871_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_913_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
if (lean_obj_tag(v_a_890_) == 0)
{
lean_object* v_snd_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_906_; 
lean_dec(v_G_868_);
v_snd_894_ = lean_ctor_get(v_____x_870_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_____x_870_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; 
v_unused_907_ = lean_ctor_get(v_____x_870_, 0);
lean_dec(v_unused_907_);
v___x_896_ = v_____x_870_;
v_isShared_897_ = v_isSharedCheck_906_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_snd_894_);
lean_dec(v_____x_870_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_906_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_a_898_; lean_object* v___x_900_; 
v_a_898_ = lean_ctor_get(v_a_890_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v_a_890_, 1);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v_a_898_);
v___x_900_ = v___x_892_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_898_);
v___x_900_ = v_reuseFailAlloc_905_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_900_);
v___x_902_ = v___x_896_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_snd_894_);
v___x_902_ = v_reuseFailAlloc_904_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; 
v___x_903_ = lean_apply_2(v_toPure_866_, lean_box(0), v___x_902_);
return v___x_903_;
}
}
}
}
else
{
lean_object* v_snd_908_; lean_object* v_a_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_del_object(v___x_892_);
lean_dec(v_toPure_866_);
v_snd_908_ = lean_ctor_get(v_____x_870_, 1);
lean_inc(v_snd_908_);
lean_dec_ref(v_____x_870_);
v_a_909_ = lean_ctor_get(v_a_890_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v_a_890_, 1);
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = lean_nat_add(v_next_867_, v___x_910_);
lean_inc_ref(v___y_869_);
v___x_912_ = lean_apply_6(v_G_868_, v___x_911_, v_a_909_, lean_box(0), lean_box(0), v___y_869_, v_snd_908_);
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed(lean_object* v_toPure_914_, lean_object* v_next_915_, lean_object* v_G_916_, lean_object* v___y_917_, lean_object* v_____x_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(v_toPure_914_, v_next_915_, v_G_916_, v___y_917_, v_____x_918_);
lean_dec_ref(v___y_917_);
lean_dec(v_next_915_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(lean_object* v_toPure_920_, lean_object* v___f_921_, lean_object* v___y_922_, lean_object* v_____x_923_){
_start:
{
lean_object* v_fst_924_; 
v_fst_924_ = lean_ctor_get(v_____x_923_, 0);
lean_inc(v_fst_924_);
if (lean_obj_tag(v_fst_924_) == 0)
{
lean_object* v_snd_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_941_; 
lean_dec(v___f_921_);
v_snd_925_ = lean_ctor_get(v_____x_923_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_____x_923_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v_____x_923_, 0);
lean_dec(v_unused_942_);
v___x_927_ = v_____x_923_;
v_isShared_928_ = v_isSharedCheck_941_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_snd_925_);
lean_dec(v_____x_923_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_941_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_940_; 
v_a_929_ = lean_ctor_get(v_fst_924_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v_fst_924_);
if (v_isSharedCheck_940_ == 0)
{
v___x_931_ = v_fst_924_;
v_isShared_932_ = v_isSharedCheck_940_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v_fst_924_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_940_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_939_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_934_);
v___x_936_ = v___x_927_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_snd_925_);
v___x_936_ = v_reuseFailAlloc_938_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; 
v___x_937_ = lean_apply_2(v_toPure_920_, lean_box(0), v___x_936_);
return v___x_937_;
}
}
}
}
}
else
{
lean_object* v_snd_943_; lean_object* v_a_944_; lean_object* v___x_945_; 
lean_dec(v_toPure_920_);
v_snd_943_ = lean_ctor_get(v_____x_923_, 1);
lean_inc(v_snd_943_);
lean_dec_ref(v_____x_923_);
v_a_944_ = lean_ctor_get(v_fst_924_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v_fst_924_, 1);
lean_inc_ref(v___y_922_);
v___x_945_ = lean_apply_3(v___f_921_, v_a_944_, v___y_922_, v_snd_943_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed(lean_object* v_toPure_946_, lean_object* v___f_947_, lean_object* v___y_948_, lean_object* v_____x_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(v_toPure_946_, v___f_947_, v___y_948_, v_____x_949_);
lean_dec_ref(v___y_948_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(lean_object* v___x_951_, lean_object* v_toPure_952_, lean_object* v_toBind_953_, lean_object* v___f_954_, lean_object* v_initialMask_955_, lean_object* v___f_956_, lean_object* v_inst_957_, lean_object* v___x_958_, lean_object* v_next_959_, lean_object* v_acc_960_, lean_object* v_h_961_, lean_object* v_G_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
uint8_t v___x_965_; 
v___x_965_ = lean_nat_dec_lt(v_next_959_, v___x_951_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec(v_G_962_);
lean_dec(v_next_959_);
lean_dec_ref(v_inst_957_);
lean_dec(v___f_956_);
lean_dec(v___f_954_);
lean_dec(v_toBind_953_);
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v_acc_960_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___y_964_);
v___x_968_ = lean_apply_2(v_toPure_952_, lean_box(0), v___x_967_);
return v___x_968_;
}
else
{
lean_object* v___f_969_; lean_object* v___y_971_; lean_object* v___x_974_; uint8_t v___x_975_; 
lean_dec_ref(v_acc_960_);
lean_inc_ref(v___y_963_);
lean_inc(v_next_959_);
lean_inc(v_toPure_952_);
v___f_969_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_969_, 0, v_toPure_952_);
lean_closure_set(v___f_969_, 1, v_next_959_);
lean_closure_set(v___f_969_, 2, v_G_962_);
lean_closure_set(v___f_969_, 3, v___y_963_);
v___x_974_ = lean_array_fget_borrowed(v_initialMask_955_, v_next_959_);
v___x_975_ = lean_unbox(v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___f_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_inc_ref(v___y_963_);
v___f_976_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_976_, 0, v_toPure_952_);
lean_closure_set(v___f_976_, 1, v___f_956_);
lean_closure_set(v___f_976_, 2, v___y_963_);
v___x_977_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(v_next_959_, v_inst_957_, v___y_964_);
lean_inc(v_toBind_953_);
v___x_978_ = lean_apply_4(v_toBind_953_, lean_box(0), lean_box(0), v___x_977_, v___f_976_);
v___y_971_ = v___x_978_;
goto v___jp_970_;
}
else
{
lean_object* v___x_979_; 
lean_dec(v_next_959_);
lean_dec_ref(v_inst_957_);
lean_dec(v_toPure_952_);
lean_inc_ref(v___y_963_);
v___x_979_ = lean_apply_3(v___f_956_, v___x_958_, v___y_963_, v___y_964_);
v___y_971_ = v___x_979_;
goto v___jp_970_;
}
v___jp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
lean_inc(v_toBind_953_);
v___x_972_ = lean_apply_4(v_toBind_953_, lean_box(0), lean_box(0), v___y_971_, v___f_954_);
v___x_973_ = lean_apply_4(v_toBind_953_, lean_box(0), lean_box(0), v___x_972_, v___f_969_);
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed(lean_object* v___x_980_, lean_object* v_toPure_981_, lean_object* v_toBind_982_, lean_object* v___f_983_, lean_object* v_initialMask_984_, lean_object* v___f_985_, lean_object* v_inst_986_, lean_object* v___x_987_, lean_object* v_next_988_, lean_object* v_acc_989_, lean_object* v_h_990_, lean_object* v_G_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(v___x_980_, v_toPure_981_, v_toBind_982_, v___f_983_, v_initialMask_984_, v___f_985_, v_inst_986_, v___x_987_, v_next_988_, v_acc_989_, v_h_990_, v_G_991_, v___y_992_, v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec_ref(v_initialMask_984_);
lean_dec(v___x_980_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(lean_object* v_toPure_998_, lean_object* v_inst_999_, lean_object* v_toBind_1000_, lean_object* v___f_1001_, lean_object* v_a_1002_, lean_object* v_____x_1003_){
_start:
{
lean_object* v_fst_1004_; 
v_fst_1004_ = lean_ctor_get(v_____x_1003_, 0);
lean_inc(v_fst_1004_);
if (lean_obj_tag(v_fst_1004_) == 0)
{
lean_object* v_snd_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v___f_1001_);
lean_dec(v_toBind_1000_);
lean_dec_ref(v_inst_999_);
v_snd_1005_ = lean_ctor_get(v_____x_1003_, 1);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_____x_1003_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v_____x_1003_, 0);
lean_dec(v_unused_1022_);
v___x_1007_ = v_____x_1003_;
v_isShared_1008_ = v_isSharedCheck_1021_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_snd_1005_);
lean_dec(v_____x_1003_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1021_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1020_; 
v_a_1009_ = lean_ctor_get(v_fst_1004_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_fst_1004_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1011_ = v_fst_1004_;
v_isShared_1012_ = v_isSharedCheck_1020_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v_fst_1004_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1020_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1014_);
v___x_1016_ = v___x_1007_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_snd_1005_);
v___x_1016_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_apply_2(v_toPure_998_, lean_box(0), v___x_1016_);
return v___x_1017_;
}
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v_snd_1024_; lean_object* v_initialMask_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___f_1029_; lean_object* v___x_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___x_6334__overap_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_a_1023_ = lean_ctor_get(v_fst_1004_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v_fst_1004_, 1);
v_snd_1024_ = lean_ctor_get(v_____x_1003_, 1);
lean_inc(v_snd_1024_);
lean_dec_ref(v_____x_1003_);
v_initialMask_1025_ = lean_ctor_get(v_a_1023_, 0);
lean_inc_ref(v_initialMask_1025_);
lean_dec(v_a_1023_);
v___x_1026_ = lean_array_get_size(v_initialMask_1025_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = lean_box(0);
lean_inc_n(v_toPure_998_, 2);
v___f_1029_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1029_, 0, v_toPure_998_);
lean_closure_set(v___f_1029_, 1, v___x_1028_);
v___x_1030_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0));
v___f_1031_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1031_, 0, v_toPure_998_);
lean_closure_set(v___f_1031_, 1, v___x_1030_);
lean_closure_set(v___f_1031_, 2, v___x_1028_);
lean_inc_n(v_toBind_1000_, 2);
lean_inc_ref(v_inst_999_);
v___f_1032_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1032_, 0, v_inst_999_);
lean_closure_set(v___f_1032_, 1, v_toBind_1000_);
lean_closure_set(v___f_1032_, 2, v___f_1031_);
v___f_1033_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed), 14, 8);
lean_closure_set(v___f_1033_, 0, v___x_1026_);
lean_closure_set(v___f_1033_, 1, v_toPure_998_);
lean_closure_set(v___f_1033_, 2, v_toBind_1000_);
lean_closure_set(v___f_1033_, 3, v___f_1001_);
lean_closure_set(v___f_1033_, 4, v_initialMask_1025_);
lean_closure_set(v___f_1033_, 5, v___f_1032_);
lean_closure_set(v___f_1033_, 6, v_inst_999_);
lean_closure_set(v___f_1033_, 7, v___x_1028_);
v___x_6334__overap_1034_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1033_, v___x_1027_, v___x_1030_, lean_box(0));
lean_inc_ref(v_a_1002_);
v___x_1035_ = lean_apply_2(v___x_6334__overap_1034_, v_a_1002_, v_snd_1024_);
v___x_1036_ = lean_apply_4(v_toBind_1000_, lean_box(0), lean_box(0), v___x_1035_, v___f_1029_);
return v___x_1036_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed(lean_object* v_toPure_1037_, lean_object* v_inst_1038_, lean_object* v_toBind_1039_, lean_object* v___f_1040_, lean_object* v_a_1041_, lean_object* v_____x_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(v_toPure_1037_, v_inst_1038_, v_toBind_1039_, v___f_1040_, v_a_1041_, v_____x_1042_);
lean_dec_ref(v_a_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(lean_object* v_inst_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_toApplicative_1047_; lean_object* v_toBind_1048_; lean_object* v_toPure_1049_; lean_object* v___f_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_toApplicative_1047_ = lean_ctor_get(v_inst_1044_, 0);
v_toBind_1048_ = lean_ctor_get(v_inst_1044_, 1);
lean_inc_n(v_toBind_1048_, 2);
v_toPure_1049_ = lean_ctor_get(v_toApplicative_1047_, 1);
lean_inc_n(v_toPure_1049_, 3);
v___f_1050_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1050_, 0, v_toPure_1049_);
lean_inc_ref_n(v_a_1045_, 2);
v___f_1051_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_1051_, 0, v_toPure_1049_);
lean_closure_set(v___f_1051_, 1, v_inst_1044_);
lean_closure_set(v___f_1051_, 2, v_toBind_1048_);
lean_closure_set(v___f_1051_, 3, v___f_1050_);
lean_closure_set(v___f_1051_, 4, v_a_1045_);
v___x_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1052_, 0, v_a_1045_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_a_1046_);
v___x_1054_ = lean_apply_2(v_toPure_1049_, lean_box(0), v___x_1053_);
v___x_1055_ = lean_apply_4(v_toBind_1048_, lean_box(0), lean_box(0), v___x_1054_, v___f_1051_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___boxed(lean_object* v_inst_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1056_, v_a_1057_, v_a_1058_);
lean_dec_ref(v_a_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(lean_object* v_m_1060_, lean_object* v_inst_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1061_, v_a_1062_, v_a_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___boxed(lean_object* v_m_1065_, lean_object* v_inst_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(v_m_1065_, v_inst_1066_, v_a_1067_, v_a_1068_);
lean_dec_ref(v_a_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0(lean_object* v_toPure_1072_, lean_object* v_____x_1073_){
_start:
{
lean_object* v_fst_1074_; 
v_fst_1074_ = lean_ctor_get(v_____x_1073_, 0);
lean_inc(v_fst_1074_);
if (lean_obj_tag(v_fst_1074_) == 0)
{
lean_object* v_snd_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1091_; 
v_snd_1075_ = lean_ctor_get(v_____x_1073_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_____x_1073_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v_____x_1073_, 0);
lean_dec(v_unused_1092_);
v___x_1077_ = v_____x_1073_;
v_isShared_1078_ = v_isSharedCheck_1091_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_snd_1075_);
lean_dec(v_____x_1073_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1091_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1090_; 
v_a_1079_ = lean_ctor_get(v_fst_1074_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_fst_1074_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1081_ = v_fst_1074_;
v_isShared_1082_ = v_isSharedCheck_1090_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v_fst_1074_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1090_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1086_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1084_);
v___x_1086_ = v___x_1077_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_snd_1075_);
v___x_1086_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_apply_2(v_toPure_1072_, lean_box(0), v___x_1086_);
return v___x_1087_;
}
}
}
}
}
else
{
lean_object* v_snd_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref_known(v_fst_1074_, 1);
v_snd_1093_ = lean_ctor_get(v_____x_1073_, 1);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_____x_1073_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; 
v_unused_1103_ = lean_ctor_get(v_____x_1073_, 0);
lean_dec(v_unused_1103_);
v___x_1095_ = v_____x_1073_;
v_isShared_1096_ = v_isSharedCheck_1102_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_snd_1093_);
lean_dec(v_____x_1073_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1102_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0));
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1097_);
v___x_1099_ = v___x_1095_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_snd_1093_);
v___x_1099_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_apply_2(v_toPure_1072_, lean_box(0), v___x_1099_);
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1(lean_object* v_toPure_1104_, lean_object* v_____x_1105_){
_start:
{
lean_object* v_fst_1106_; 
v_fst_1106_ = lean_ctor_get(v_____x_1105_, 0);
lean_inc(v_fst_1106_);
if (lean_obj_tag(v_fst_1106_) == 0)
{
lean_object* v_snd_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1123_; 
v_snd_1107_ = lean_ctor_get(v_____x_1105_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_____x_1105_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_____x_1105_, 0);
lean_dec(v_unused_1124_);
v___x_1109_ = v_____x_1105_;
v_isShared_1110_ = v_isSharedCheck_1123_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_snd_1107_);
lean_dec(v_____x_1105_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1123_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1122_; 
v_a_1111_ = lean_ctor_get(v_fst_1106_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_fst_1106_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1113_ = v_fst_1106_;
v_isShared_1114_ = v_isSharedCheck_1122_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v_fst_1106_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1122_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1118_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1116_);
v___x_1118_ = v___x_1109_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_snd_1107_);
v___x_1118_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_apply_2(v_toPure_1104_, lean_box(0), v___x_1118_);
return v___x_1119_;
}
}
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1171_; 
v_a_1125_ = lean_ctor_get(v_fst_1106_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_fst_1106_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1127_ = v_fst_1106_;
v_isShared_1128_ = v_isSharedCheck_1171_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v_fst_1106_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1171_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
if (lean_obj_tag(v_a_1125_) == 0)
{
lean_object* v_snd_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1148_; 
v_snd_1129_ = lean_ctor_get(v_____x_1105_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_____x_1105_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v_____x_1105_, 0);
lean_dec(v_unused_1149_);
v___x_1131_ = v_____x_1105_;
v_isShared_1132_ = v_isSharedCheck_1148_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_snd_1129_);
lean_dec(v_____x_1105_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1148_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1147_; 
v_a_1133_ = lean_ctor_get(v_a_1125_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_a_1125_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1135_ = v_a_1125_;
v_isShared_1136_ = v_isSharedCheck_1147_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v_a_1125_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1147_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 1);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1140_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1138_);
v___x_1140_ = v___x_1127_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1140_);
v___x_1142_ = v___x_1131_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_snd_1129_);
v___x_1142_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_apply_2(v_toPure_1104_, lean_box(0), v___x_1142_);
return v___x_1143_;
}
}
}
}
}
}
else
{
lean_object* v_snd_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1169_; 
v_snd_1150_ = lean_ctor_get(v_____x_1105_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_____x_1105_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v_____x_1105_, 0);
lean_dec(v_unused_1170_);
v___x_1152_ = v_____x_1105_;
v_isShared_1153_ = v_isSharedCheck_1169_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_snd_1150_);
lean_dec(v_____x_1105_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1169_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1168_; 
v_a_1154_ = lean_ctor_get(v_a_1125_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_a_1125_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1156_ = v_a_1125_;
v_isShared_1157_ = v_isSharedCheck_1168_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v_a_1125_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1168_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 0);
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1161_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1159_);
v___x_1161_ = v___x_1127_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1161_);
v___x_1163_ = v___x_1152_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_snd_1150_);
v___x_1163_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_apply_2(v_toPure_1104_, lean_box(0), v___x_1163_);
return v___x_1164_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2(lean_object* v_toPure_1172_, lean_object* v___x_1173_, lean_object* v_____x_1174_){
_start:
{
lean_object* v_fst_1175_; 
v_fst_1175_ = lean_ctor_get(v_____x_1174_, 0);
lean_inc(v_fst_1175_);
if (lean_obj_tag(v_fst_1175_) == 0)
{
lean_object* v_snd_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v___x_1173_);
v_snd_1176_ = lean_ctor_get(v_____x_1174_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_____x_1174_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; 
v_unused_1193_ = lean_ctor_get(v_____x_1174_, 0);
lean_dec(v_unused_1193_);
v___x_1178_ = v_____x_1174_;
v_isShared_1179_ = v_isSharedCheck_1192_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_snd_1176_);
lean_dec(v_____x_1174_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1192_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1191_; 
v_a_1180_ = lean_ctor_get(v_fst_1175_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_fst_1175_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1182_ = v_fst_1175_;
v_isShared_1183_ = v_isSharedCheck_1191_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v_fst_1175_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1191_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1185_);
v___x_1187_ = v___x_1178_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_snd_1176_);
v___x_1187_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_apply_2(v_toPure_1172_, lean_box(0), v___x_1187_);
return v___x_1188_;
}
}
}
}
}
else
{
lean_object* v_snd_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1211_; 
v_snd_1194_ = lean_ctor_get(v_____x_1174_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_____x_1174_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v_____x_1174_, 0);
lean_dec(v_unused_1212_);
v___x_1196_ = v_____x_1174_;
v_isShared_1197_ = v_isSharedCheck_1211_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_snd_1194_);
lean_dec(v_____x_1174_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1211_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1209_; 
v_isSharedCheck_1209_ = !lean_is_exclusive(v_fst_1175_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v_fst_1175_, 0);
lean_dec(v_unused_1210_);
v___x_1199_ = v_fst_1175_;
v_isShared_1200_ = v_isSharedCheck_1209_;
goto v_resetjp_1198_;
}
else
{
lean_dec(v_fst_1175_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1209_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1173_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1201_);
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1203_);
v___x_1205_ = v___x_1196_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_snd_1194_);
v___x_1205_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_apply_2(v_toPure_1172_, lean_box(0), v___x_1205_);
return v___x_1206_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(lean_object* v_toPure_1213_, lean_object* v___x_1214_, lean_object* v_inst_1215_, lean_object* v_toBind_1216_, lean_object* v___f_1217_, lean_object* v___x_1218_, lean_object* v_____x_1219_){
_start:
{
lean_object* v_fst_1220_; 
v_fst_1220_ = lean_ctor_get(v_____x_1219_, 0);
lean_inc(v_fst_1220_);
if (lean_obj_tag(v_fst_1220_) == 0)
{
lean_object* v_snd_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v___x_1218_);
lean_dec(v___f_1217_);
lean_dec(v_toBind_1216_);
lean_dec_ref(v_inst_1215_);
v_snd_1221_ = lean_ctor_get(v_____x_1219_, 1);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_____x_1219_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v_____x_1219_, 0);
lean_dec(v_unused_1238_);
v___x_1223_ = v_____x_1219_;
v_isShared_1224_ = v_isSharedCheck_1237_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_snd_1221_);
lean_dec(v_____x_1219_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1237_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1236_; 
v_a_1225_ = lean_ctor_get(v_fst_1220_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_fst_1220_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1227_ = v_fst_1220_;
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v_fst_1220_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1232_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1230_);
v___x_1232_ = v___x_1223_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1230_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_snd_1221_);
v___x_1232_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_apply_2(v_toPure_1213_, lean_box(0), v___x_1232_);
return v___x_1233_;
}
}
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1261_; 
v_a_1239_ = lean_ctor_get(v_fst_1220_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_fst_1220_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1241_ = v_fst_1220_;
v_isShared_1242_ = v_isSharedCheck_1261_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v_fst_1220_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1261_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
uint8_t v___x_1243_; 
v___x_1243_ = lean_unbox(v_a_1239_);
lean_dec(v_a_1239_);
if (v___x_1243_ == 0)
{
lean_object* v_snd_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_del_object(v___x_1241_);
lean_dec(v___x_1218_);
lean_dec(v_toPure_1213_);
v_snd_1244_ = lean_ctor_get(v_____x_1219_, 1);
lean_inc(v_snd_1244_);
lean_dec_ref(v_____x_1219_);
v___x_1245_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v___x_1214_, v_inst_1215_, v_snd_1244_);
v___x_1246_ = lean_apply_4(v_toBind_1216_, lean_box(0), lean_box(0), v___x_1245_, v___f_1217_);
return v___x_1246_;
}
else
{
lean_object* v_snd_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v___f_1217_);
lean_dec(v_toBind_1216_);
lean_dec_ref(v_inst_1215_);
v_snd_1247_ = lean_ctor_get(v_____x_1219_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_____x_1219_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v_____x_1219_, 0);
lean_dec(v_unused_1260_);
v___x_1249_ = v_____x_1219_;
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_snd_1247_);
lean_dec(v_____x_1219_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1218_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1251_);
v___x_1253_ = v___x_1241_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1255_; 
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1253_);
v___x_1255_ = v___x_1249_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_snd_1247_);
v___x_1255_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_apply_2(v_toPure_1213_, lean_box(0), v___x_1255_);
return v___x_1256_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed(lean_object* v_toPure_1262_, lean_object* v___x_1263_, lean_object* v_inst_1264_, lean_object* v_toBind_1265_, lean_object* v___f_1266_, lean_object* v___x_1267_, lean_object* v_____x_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(v_toPure_1262_, v___x_1263_, v_inst_1264_, v_toBind_1265_, v___f_1266_, v___x_1267_, v_____x_1268_);
lean_dec(v___x_1263_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(lean_object* v_toPure_1270_, lean_object* v_inst_1271_, lean_object* v___y_1272_, lean_object* v_toBind_1273_, lean_object* v___f_1274_, lean_object* v_____x_1275_){
_start:
{
lean_object* v_fst_1276_; 
v_fst_1276_ = lean_ctor_get(v_____x_1275_, 0);
lean_inc(v_fst_1276_);
if (lean_obj_tag(v_fst_1276_) == 0)
{
lean_object* v_snd_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v___f_1274_);
lean_dec(v_toBind_1273_);
lean_dec_ref(v_inst_1271_);
v_snd_1277_ = lean_ctor_get(v_____x_1275_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_____x_1275_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v_____x_1275_, 0);
lean_dec(v_unused_1294_);
v___x_1279_ = v_____x_1275_;
v_isShared_1280_ = v_isSharedCheck_1293_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_snd_1277_);
lean_dec(v_____x_1275_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1293_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1292_; 
v_a_1281_ = lean_ctor_get(v_fst_1276_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_fst_1276_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1283_ = v_fst_1276_;
v_isShared_1284_ = v_isSharedCheck_1292_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v_fst_1276_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1292_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1288_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1286_);
v___x_1288_ = v___x_1279_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_snd_1277_);
v___x_1288_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_apply_2(v_toPure_1270_, lean_box(0), v___x_1288_);
return v___x_1289_;
}
}
}
}
}
else
{
lean_object* v_snd_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec_ref_known(v_fst_1276_, 1);
lean_dec(v_toPure_1270_);
v_snd_1295_ = lean_ctor_get(v_____x_1275_, 1);
lean_inc(v_snd_1295_);
lean_dec_ref(v_____x_1275_);
v___x_1296_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_1271_, v___y_1272_, v_snd_1295_);
v___x_1297_ = lean_apply_4(v_toBind_1273_, lean_box(0), lean_box(0), v___x_1296_, v___f_1274_);
return v___x_1297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed(lean_object* v_toPure_1298_, lean_object* v_inst_1299_, lean_object* v___y_1300_, lean_object* v_toBind_1301_, lean_object* v___f_1302_, lean_object* v_____x_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(v_toPure_1298_, v_inst_1299_, v___y_1300_, v_toBind_1301_, v___f_1302_, v_____x_1303_);
lean_dec_ref(v___y_1300_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(lean_object* v_toPure_1305_, lean_object* v___x_1306_, lean_object* v_inst_1307_, lean_object* v_toBind_1308_, lean_object* v___f_1309_, lean_object* v___y_1310_, lean_object* v_____x_1311_){
_start:
{
lean_object* v_fst_1312_; 
v_fst_1312_ = lean_ctor_get(v_____x_1311_, 0);
lean_inc(v_fst_1312_);
if (lean_obj_tag(v_fst_1312_) == 0)
{
lean_object* v_snd_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v___f_1309_);
lean_dec(v_toBind_1308_);
lean_dec_ref(v_inst_1307_);
lean_dec(v___x_1306_);
v_snd_1313_ = lean_ctor_get(v_____x_1311_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_____x_1311_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v_____x_1311_, 0);
lean_dec(v_unused_1330_);
v___x_1315_ = v_____x_1311_;
v_isShared_1316_ = v_isSharedCheck_1329_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_snd_1313_);
lean_dec(v_____x_1311_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1329_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1328_; 
v_a_1317_ = lean_ctor_get(v_fst_1312_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_fst_1312_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1319_ = v_fst_1312_;
v_isShared_1320_ = v_isSharedCheck_1328_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v_fst_1312_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1328_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1324_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v___x_1322_);
v___x_1324_ = v___x_1315_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_snd_1313_);
v___x_1324_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_apply_2(v_toPure_1305_, lean_box(0), v___x_1324_);
return v___x_1325_;
}
}
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v_snd_1332_; lean_object* v_added_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___f_1336_; lean_object* v___f_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_a_1331_ = lean_ctor_get(v_fst_1312_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v_fst_1312_, 1);
v_snd_1332_ = lean_ctor_get(v_____x_1311_, 1);
lean_inc(v_snd_1332_);
lean_dec_ref(v_____x_1311_);
v_added_1333_ = lean_ctor_get(v_a_1331_, 1);
lean_inc_ref(v_added_1333_);
lean_dec(v_a_1331_);
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = lean_array_get(v___x_1334_, v_added_1333_, v___x_1306_);
lean_dec_ref(v_added_1333_);
lean_inc_n(v_toBind_1308_, 2);
lean_inc_ref_n(v_inst_1307_, 2);
lean_inc(v___x_1335_);
lean_inc(v_toPure_1305_);
v___f_1336_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1336_, 0, v_toPure_1305_);
lean_closure_set(v___f_1336_, 1, v___x_1335_);
lean_closure_set(v___f_1336_, 2, v_inst_1307_);
lean_closure_set(v___f_1336_, 3, v_toBind_1308_);
lean_closure_set(v___f_1336_, 4, v___f_1309_);
lean_closure_set(v___f_1336_, 5, v___x_1306_);
lean_inc_ref(v___y_1310_);
v___f_1337_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_1337_, 0, v_toPure_1305_);
lean_closure_set(v___f_1337_, 1, v_inst_1307_);
lean_closure_set(v___f_1337_, 2, v___y_1310_);
lean_closure_set(v___f_1337_, 3, v_toBind_1308_);
lean_closure_set(v___f_1337_, 4, v___f_1336_);
v___x_1338_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v___x_1335_, v_inst_1307_, v_snd_1332_);
lean_dec(v___x_1335_);
v___x_1339_ = lean_apply_4(v_toBind_1308_, lean_box(0), lean_box(0), v___x_1338_, v___f_1337_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed(lean_object* v_toPure_1340_, lean_object* v___x_1341_, lean_object* v_inst_1342_, lean_object* v_toBind_1343_, lean_object* v___f_1344_, lean_object* v___y_1345_, lean_object* v_____x_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(v_toPure_1340_, v___x_1341_, v_inst_1342_, v_toBind_1343_, v___f_1344_, v___y_1345_, v_____x_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7(lean_object* v_toPure_1348_, lean_object* v_toBind_1349_, lean_object* v___f_1350_, lean_object* v___x_1351_, lean_object* v_inst_1352_, lean_object* v_b_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = lean_nat_dec_lt(v___x_1356_, v_b_1353_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec_ref(v_inst_1352_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_b_1353_);
v___x_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v___y_1355_);
v___x_1361_ = lean_apply_2(v_toPure_1348_, lean_box(0), v___x_1360_);
v___x_1362_ = lean_apply_4(v_toBind_1349_, lean_box(0), lean_box(0), v___x_1361_, v___f_1350_);
return v___x_1362_;
}
else
{
lean_object* v___x_1363_; lean_object* v___f_1364_; lean_object* v___f_1365_; lean_object* v___f_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1363_ = lean_nat_sub(v_b_1353_, v___x_1351_);
lean_dec(v_b_1353_);
lean_inc(v___x_1363_);
lean_inc_n(v_toPure_1348_, 3);
v___f_1364_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1364_, 0, v_toPure_1348_);
lean_closure_set(v___f_1364_, 1, v___x_1363_);
lean_inc_ref(v___y_1354_);
lean_inc_n(v_toBind_1349_, 3);
v___f_1365_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1365_, 0, v_toPure_1348_);
lean_closure_set(v___f_1365_, 1, v___x_1363_);
lean_closure_set(v___f_1365_, 2, v_inst_1352_);
lean_closure_set(v___f_1365_, 3, v_toBind_1349_);
lean_closure_set(v___f_1365_, 4, v___f_1364_);
lean_closure_set(v___f_1365_, 5, v___y_1354_);
v___f_1366_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1366_, 0, v_toPure_1348_);
lean_inc_ref(v___y_1355_);
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___y_1355_);
lean_ctor_set(v___x_1367_, 1, v___y_1355_);
v___x_1368_ = lean_apply_2(v_toPure_1348_, lean_box(0), v___x_1367_);
v___x_1369_ = lean_apply_4(v_toBind_1349_, lean_box(0), lean_box(0), v___x_1368_, v___f_1366_);
v___x_1370_ = lean_apply_4(v_toBind_1349_, lean_box(0), lean_box(0), v___x_1369_, v___f_1365_);
v___x_1371_ = lean_apply_4(v_toBind_1349_, lean_box(0), lean_box(0), v___x_1370_, v___f_1350_);
return v___x_1371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed(lean_object* v_toPure_1372_, lean_object* v_toBind_1373_, lean_object* v___f_1374_, lean_object* v___x_1375_, lean_object* v_inst_1376_, lean_object* v_b_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7(v_toPure_1372_, v_toBind_1373_, v___f_1374_, v___x_1375_, v_inst_1376_, v_b_1377_, v___y_1378_, v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___x_1375_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(lean_object* v_toPure_1381_, lean_object* v_toBind_1382_, lean_object* v___f_1383_, lean_object* v_inst_1384_, lean_object* v___x_1385_, lean_object* v_a_1386_, lean_object* v___f_1387_, lean_object* v_____x_1388_){
_start:
{
lean_object* v_fst_1389_; 
v_fst_1389_ = lean_ctor_get(v_____x_1388_, 0);
lean_inc(v_fst_1389_);
if (lean_obj_tag(v_fst_1389_) == 0)
{
lean_object* v_snd_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v___f_1387_);
lean_dec_ref(v___x_1385_);
lean_dec_ref(v_inst_1384_);
lean_dec(v___f_1383_);
lean_dec(v_toBind_1382_);
v_snd_1390_ = lean_ctor_get(v_____x_1388_, 1);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_____x_1388_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; 
v_unused_1407_ = lean_ctor_get(v_____x_1388_, 0);
lean_dec(v_unused_1407_);
v___x_1392_ = v_____x_1388_;
v_isShared_1393_ = v_isSharedCheck_1406_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_snd_1390_);
lean_dec(v_____x_1388_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1406_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1405_; 
v_a_1394_ = lean_ctor_get(v_fst_1389_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_fst_1389_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1396_ = v_fst_1389_;
v_isShared_1397_ = v_isSharedCheck_1405_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v_fst_1389_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1405_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1401_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1399_);
v___x_1401_ = v___x_1392_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_snd_1390_);
v___x_1401_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_apply_2(v_toPure_1381_, lean_box(0), v___x_1401_);
return v___x_1402_;
}
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v_snd_1409_; lean_object* v_added_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___f_1413_; lean_object* v___x_1414_; lean_object* v___x_6143__overap_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_a_1408_ = lean_ctor_get(v_fst_1389_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v_fst_1389_, 1);
v_snd_1409_ = lean_ctor_get(v_____x_1388_, 1);
lean_inc(v_snd_1409_);
lean_dec_ref(v_____x_1388_);
v_added_1410_ = lean_ctor_get(v_a_1408_, 1);
lean_inc_ref(v_added_1410_);
lean_dec(v_a_1408_);
v___x_1411_ = lean_array_get_size(v_added_1410_);
lean_dec_ref(v_added_1410_);
v___x_1412_ = lean_unsigned_to_nat(1u);
lean_inc(v_toBind_1382_);
v___f_1413_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed), 8, 5);
lean_closure_set(v___f_1413_, 0, v_toPure_1381_);
lean_closure_set(v___f_1413_, 1, v_toBind_1382_);
lean_closure_set(v___f_1413_, 2, v___f_1383_);
lean_closure_set(v___f_1413_, 3, v___x_1412_);
lean_closure_set(v___f_1413_, 4, v_inst_1384_);
v___x_1414_ = lean_nat_sub(v___x_1411_, v___x_1412_);
v___x_6143__overap_1415_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_1385_, v___f_1413_, v___x_1414_);
lean_inc_ref(v_a_1386_);
v___x_1416_ = lean_apply_2(v___x_6143__overap_1415_, v_a_1386_, v_snd_1409_);
v___x_1417_ = lean_apply_4(v_toBind_1382_, lean_box(0), lean_box(0), v___x_1416_, v___f_1387_);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed(lean_object* v_toPure_1418_, lean_object* v_toBind_1419_, lean_object* v___f_1420_, lean_object* v_inst_1421_, lean_object* v___x_1422_, lean_object* v_a_1423_, lean_object* v___f_1424_, lean_object* v_____x_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(v_toPure_1418_, v_toBind_1419_, v___f_1420_, v_inst_1421_, v___x_1422_, v_a_1423_, v___f_1424_, v_____x_1425_);
lean_dec_ref(v_a_1423_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(lean_object* v_inst_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v___f_1430_; lean_object* v___f_1431_; lean_object* v___f_1432_; lean_object* v___f_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_toApplicative_1451_; lean_object* v_toBind_1452_; lean_object* v_toPure_1453_; lean_object* v___f_1454_; lean_object* v___f_1455_; lean_object* v___f_1456_; lean_object* v___f_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_inc_ref_n(v_inst_1427_, 7);
v___f_1430_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1430_, 0, v_inst_1427_);
v___f_1431_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1431_, 0, v_inst_1427_);
v___f_1432_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1432_, 0, v_inst_1427_);
v___f_1433_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1433_, 0, v_inst_1427_);
v___x_1434_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1434_, 0, lean_box(0));
lean_closure_set(v___x_1434_, 1, lean_box(0));
lean_closure_set(v___x_1434_, 2, v_inst_1427_);
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
lean_ctor_set(v___x_1435_, 1, v___f_1430_);
v___x_1436_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1436_, 0, lean_box(0));
lean_closure_set(v___x_1436_, 1, lean_box(0));
lean_closure_set(v___x_1436_, 2, v_inst_1427_);
v___x_1437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
lean_ctor_set(v___x_1437_, 2, v___f_1431_);
lean_ctor_set(v___x_1437_, 3, v___f_1432_);
lean_ctor_set(v___x_1437_, 4, v___f_1433_);
v___x_1438_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1438_, 0, lean_box(0));
lean_closure_set(v___x_1438_, 1, lean_box(0));
lean_closure_set(v___x_1438_, 2, v_inst_1427_);
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
lean_inc_ref_n(v___x_1439_, 6);
v___f_1440_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1440_, 0, v___x_1439_);
v___f_1441_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1441_, 0, v___x_1439_);
v___f_1442_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1442_, 0, v___x_1439_);
v___f_1443_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1443_, 0, v___x_1439_);
v___x_1444_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1444_, 0, lean_box(0));
lean_closure_set(v___x_1444_, 1, lean_box(0));
lean_closure_set(v___x_1444_, 2, v___x_1439_);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v___f_1440_);
v___x_1446_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1446_, 0, lean_box(0));
lean_closure_set(v___x_1446_, 1, lean_box(0));
lean_closure_set(v___x_1446_, 2, v___x_1439_);
v___x_1447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
lean_ctor_set(v___x_1447_, 2, v___f_1441_);
lean_ctor_set(v___x_1447_, 3, v___f_1442_);
lean_ctor_set(v___x_1447_, 4, v___f_1443_);
v___x_1448_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1448_, 0, lean_box(0));
lean_closure_set(v___x_1448_, 1, lean_box(0));
lean_closure_set(v___x_1448_, 2, v___x_1439_);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = l_ReaderT_instMonad___redArg(v___x_1449_);
v_toApplicative_1451_ = lean_ctor_get(v_inst_1427_, 0);
v_toBind_1452_ = lean_ctor_get(v_inst_1427_, 1);
lean_inc_n(v_toBind_1452_, 3);
v_toPure_1453_ = lean_ctor_get(v_toApplicative_1451_, 1);
lean_inc_n(v_toPure_1453_, 5);
v___f_1454_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1454_, 0, v_toPure_1453_);
v___f_1455_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1455_, 0, v_toPure_1453_);
lean_inc_ref(v_a_1428_);
v___f_1456_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed), 8, 7);
lean_closure_set(v___f_1456_, 0, v_toPure_1453_);
lean_closure_set(v___f_1456_, 1, v_toBind_1452_);
lean_closure_set(v___f_1456_, 2, v___f_1455_);
lean_closure_set(v___f_1456_, 3, v_inst_1427_);
lean_closure_set(v___f_1456_, 4, v___x_1450_);
lean_closure_set(v___f_1456_, 5, v_a_1428_);
lean_closure_set(v___f_1456_, 6, v___f_1454_);
v___f_1457_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1457_, 0, v_toPure_1453_);
lean_inc_ref(v_a_1429_);
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v_a_1429_);
lean_ctor_set(v___x_1458_, 1, v_a_1429_);
v___x_1459_ = lean_apply_2(v_toPure_1453_, lean_box(0), v___x_1458_);
v___x_1460_ = lean_apply_4(v_toBind_1452_, lean_box(0), lean_box(0), v___x_1459_, v___f_1457_);
v___x_1461_ = lean_apply_4(v_toBind_1452_, lean_box(0), lean_box(0), v___x_1460_, v___f_1456_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___boxed(lean_object* v_inst_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1462_, v_a_1463_, v_a_1464_);
lean_dec_ref(v_a_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(lean_object* v_m_1466_, lean_object* v_inst_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1467_, v_a_1468_, v_a_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___boxed(lean_object* v_m_1471_, lean_object* v_inst_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(v_m_1471_, v_inst_1472_, v_a_1473_, v_a_1474_);
lean_dec_ref(v_a_1473_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(lean_object* v_toApplicative_1476_, lean_object* v_inst_1477_, lean_object* v_a_1478_, lean_object* v_____x_1479_){
_start:
{
lean_object* v_fst_1480_; 
v_fst_1480_ = lean_ctor_get(v_____x_1479_, 0);
lean_inc(v_fst_1480_);
if (lean_obj_tag(v_fst_1480_) == 0)
{
lean_object* v_snd_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref(v_inst_1477_);
v_snd_1481_ = lean_ctor_get(v_____x_1479_, 1);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_____x_1479_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; 
v_unused_1499_ = lean_ctor_get(v_____x_1479_, 0);
lean_dec(v_unused_1499_);
v___x_1483_ = v_____x_1479_;
v_isShared_1484_ = v_isSharedCheck_1498_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_snd_1481_);
lean_dec(v_____x_1479_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1498_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1497_; 
v_a_1485_ = lean_ctor_get(v_fst_1480_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_fst_1480_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1487_ = v_fst_1480_;
v_isShared_1488_ = v_isSharedCheck_1497_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v_fst_1480_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1497_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_toPure_1489_; lean_object* v___x_1491_; 
v_toPure_1489_ = lean_ctor_get(v_toApplicative_1476_, 1);
lean_inc(v_toPure_1489_);
lean_dec_ref(v_toApplicative_1476_);
if (v_isShared_1488_ == 0)
{
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1485_);
v___x_1491_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1491_);
v___x_1493_ = v___x_1483_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_snd_1481_);
v___x_1493_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_apply_2(v_toPure_1489_, lean_box(0), v___x_1493_);
return v___x_1494_;
}
}
}
}
}
else
{
lean_object* v_a_1500_; uint8_t v_found_1501_; 
v_a_1500_ = lean_ctor_get(v_fst_1480_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v_fst_1480_, 1);
v_found_1501_ = lean_ctor_get_uint8(v_a_1500_, sizeof(void*)*3);
lean_dec(v_a_1500_);
if (v_found_1501_ == 0)
{
lean_object* v_snd_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1512_; 
lean_dec_ref(v_inst_1477_);
v_snd_1502_ = lean_ctor_get(v_____x_1479_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_____x_1479_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v_____x_1479_, 0);
lean_dec(v_unused_1513_);
v___x_1504_ = v_____x_1479_;
v_isShared_1505_ = v_isSharedCheck_1512_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_snd_1502_);
lean_dec(v_____x_1479_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1512_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v_toPure_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v_toPure_1506_ = lean_ctor_get(v_toApplicative_1476_, 1);
lean_inc(v_toPure_1506_);
lean_dec_ref(v_toApplicative_1476_);
v___x_1507_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0));
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1507_);
v___x_1509_ = v___x_1504_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_snd_1502_);
v___x_1509_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_apply_2(v_toPure_1506_, lean_box(0), v___x_1509_);
return v___x_1510_;
}
}
}
else
{
lean_object* v_snd_1514_; lean_object* v___x_1515_; 
lean_dec_ref(v_toApplicative_1476_);
v_snd_1514_ = lean_ctor_get(v_____x_1479_, 1);
lean_inc(v_snd_1514_);
lean_dec_ref(v_____x_1479_);
v___x_1515_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1477_, v_a_1478_, v_snd_1514_);
return v___x_1515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed(lean_object* v_toApplicative_1516_, lean_object* v_inst_1517_, lean_object* v_a_1518_, lean_object* v_____x_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(v_toApplicative_1516_, v_inst_1517_, v_a_1518_, v_____x_1519_);
lean_dec_ref(v_a_1518_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2(lean_object* v_toApplicative_1521_, lean_object* v_toBind_1522_, lean_object* v___f_1523_, lean_object* v_____x_1524_){
_start:
{
lean_object* v_fst_1525_; 
v_fst_1525_ = lean_ctor_get(v_____x_1524_, 0);
if (lean_obj_tag(v_fst_1525_) == 0)
{
lean_object* v_toPure_1526_; lean_object* v___x_1527_; 
lean_dec(v___f_1523_);
lean_dec(v_toBind_1522_);
v_toPure_1526_ = lean_ctor_get(v_toApplicative_1521_, 1);
lean_inc(v_toPure_1526_);
lean_dec_ref(v_toApplicative_1521_);
v___x_1527_ = lean_apply_2(v_toPure_1526_, lean_box(0), v_____x_1524_);
return v___x_1527_;
}
else
{
lean_object* v_snd_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1540_; 
v_snd_1528_ = lean_ctor_get(v_____x_1524_, 1);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_____x_1524_);
if (v_isSharedCheck_1540_ == 0)
{
lean_object* v_unused_1541_; 
v_unused_1541_ = lean_ctor_get(v_____x_1524_, 0);
lean_dec(v_unused_1541_);
v___x_1530_ = v_____x_1524_;
v_isShared_1531_ = v_isSharedCheck_1540_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_snd_1528_);
lean_dec(v_____x_1524_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1540_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v_toPure_1532_; lean_object* v___f_1533_; lean_object* v___x_1535_; 
v_toPure_1532_ = lean_ctor_get(v_toApplicative_1521_, 1);
lean_inc_n(v_toPure_1532_, 2);
lean_dec_ref(v_toApplicative_1521_);
v___f_1533_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1533_, 0, v_toPure_1532_);
lean_inc(v_snd_1528_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v_snd_1528_);
v___x_1535_ = v___x_1530_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_snd_1528_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_snd_1528_);
v___x_1535_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1536_ = lean_apply_2(v_toPure_1532_, lean_box(0), v___x_1535_);
lean_inc(v_toBind_1522_);
v___x_1537_ = lean_apply_4(v_toBind_1522_, lean_box(0), lean_box(0), v___x_1536_, v___f_1533_);
v___x_1538_ = lean_apply_4(v_toBind_1522_, lean_box(0), lean_box(0), v___x_1537_, v___f_1523_);
return v___x_1538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(lean_object* v_inst_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_toApplicative_1545_; lean_object* v_toBind_1546_; lean_object* v___f_1547_; lean_object* v___f_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_toApplicative_1545_ = lean_ctor_get(v_inst_1542_, 0);
v_toBind_1546_ = lean_ctor_get(v_inst_1542_, 1);
lean_inc_n(v_toBind_1546_, 2);
lean_inc_ref(v_a_1543_);
lean_inc_ref(v_inst_1542_);
lean_inc_ref_n(v_toApplicative_1545_, 2);
v___f_1547_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1547_, 0, v_toApplicative_1545_);
lean_closure_set(v___f_1547_, 1, v_inst_1542_);
lean_closure_set(v___f_1547_, 2, v_a_1543_);
v___f_1548_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1548_, 0, v_toApplicative_1545_);
lean_closure_set(v___f_1548_, 1, v_toBind_1546_);
lean_closure_set(v___f_1548_, 2, v___f_1547_);
v___x_1549_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1542_, v_a_1543_, v_a_1544_);
v___x_1550_ = lean_apply_4(v_toBind_1546_, lean_box(0), lean_box(0), v___x_1549_, v___f_1548_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___boxed(lean_object* v_inst_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1551_, v_a_1552_, v_a_1553_);
lean_dec_ref(v_a_1552_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(lean_object* v_m_1555_, lean_object* v_inst_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1556_, v_a_1557_, v_a_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___boxed(lean_object* v_m_1560_, lean_object* v_inst_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(v_m_1560_, v_inst_1561_, v_a_1562_, v_a_1563_);
lean_dec_ref(v_a_1562_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0(lean_object* v_toApplicative_1565_, lean_object* v_____x_1566_){
_start:
{
lean_object* v_snd_1567_; lean_object* v_fst_1568_; lean_object* v_cur_1569_; lean_object* v_numCalls_1570_; uint8_t v_found_1571_; uint8_t v___y_1573_; 
v_snd_1567_ = lean_ctor_get(v_____x_1566_, 1);
v_fst_1568_ = lean_ctor_get(v_____x_1566_, 0);
v_cur_1569_ = lean_ctor_get(v_snd_1567_, 0);
v_numCalls_1570_ = lean_ctor_get(v_snd_1567_, 2);
v_found_1571_ = lean_ctor_get_uint8(v_snd_1567_, sizeof(void*)*3);
if (v_found_1571_ == 0)
{
uint8_t v___x_1577_; 
v___x_1577_ = 0;
v___y_1573_ = v___x_1577_;
goto v___jp_1572_;
}
else
{
if (lean_obj_tag(v_fst_1568_) == 0)
{
uint8_t v___x_1578_; 
v___x_1578_ = 1;
v___y_1573_ = v___x_1578_;
goto v___jp_1572_;
}
else
{
uint8_t v___x_1579_; 
v___x_1579_ = 2;
v___y_1573_ = v___x_1579_;
goto v___jp_1572_;
}
}
v___jp_1572_:
{
lean_object* v_toPure_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_toPure_1574_ = lean_ctor_get(v_toApplicative_1565_, 1);
lean_inc(v_toPure_1574_);
lean_dec_ref(v_toApplicative_1565_);
lean_inc(v_numCalls_1570_);
lean_inc_ref(v_cur_1569_);
v___x_1575_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1575_, 0, v_cur_1569_);
lean_ctor_set(v___x_1575_, 1, v_numCalls_1570_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2, v___y_1573_);
v___x_1576_ = lean_apply_2(v_toPure_1574_, lean_box(0), v___x_1575_);
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed(lean_object* v_toApplicative_1580_, lean_object* v_____x_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__0(v_toApplicative_1580_, v_____x_1581_);
lean_dec_ref(v_____x_1581_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1(lean_object* v_initialMask_1585_, lean_object* v_test_1586_, lean_object* v_maxCalls_1587_, lean_object* v_inst_1588_, lean_object* v_toBind_1589_, lean_object* v___f_1590_, lean_object* v_toApplicative_1591_, uint8_t v_____do__lift_1592_){
_start:
{
if (v_____do__lift_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec_ref(v_toApplicative_1591_);
lean_inc_ref(v_initialMask_1585_);
v___x_1593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1593_, 0, v_initialMask_1585_);
lean_ctor_set(v___x_1593_, 1, v_test_1586_);
lean_ctor_set(v___x_1593_, 2, v_maxCalls_1587_);
v___x_1594_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0));
v___x_1595_ = lean_unsigned_to_nat(1u);
v___x_1596_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1596_, 0, v_initialMask_1585_);
lean_ctor_set(v___x_1596_, 1, v___x_1594_);
lean_ctor_set(v___x_1596_, 2, v___x_1595_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*3, v_____do__lift_1592_);
v___x_1597_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1588_, v___x_1593_, v___x_1596_);
lean_dec_ref_known(v___x_1593_, 3);
v___x_1598_ = lean_apply_4(v_toBind_1589_, lean_box(0), lean_box(0), v___x_1597_, v___f_1590_);
return v___x_1598_;
}
else
{
lean_object* v_toPure_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v___f_1590_);
lean_dec(v_toBind_1589_);
lean_dec_ref(v_inst_1588_);
lean_dec(v_maxCalls_1587_);
lean_dec(v_test_1586_);
v_toPure_1599_ = lean_ctor_get(v_toApplicative_1591_, 1);
lean_inc(v_toPure_1599_);
lean_dec_ref(v_toApplicative_1591_);
v___x_1600_ = 2;
v___x_1601_ = lean_unsigned_to_nat(1u);
v___x_1602_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1602_, 0, v_initialMask_1585_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*2, v___x_1600_);
v___x_1603_ = lean_apply_2(v_toPure_1599_, lean_box(0), v___x_1602_);
return v___x_1603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed(lean_object* v_initialMask_1604_, lean_object* v_test_1605_, lean_object* v_maxCalls_1606_, lean_object* v_inst_1607_, lean_object* v_toBind_1608_, lean_object* v___f_1609_, lean_object* v_toApplicative_1610_, lean_object* v_____do__lift_1611_){
_start:
{
uint8_t v_____do__lift_277__boxed_1612_; lean_object* v_res_1613_; 
v_____do__lift_277__boxed_1612_ = lean_unbox(v_____do__lift_1611_);
v_res_1613_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__1(v_initialMask_1604_, v_test_1605_, v_maxCalls_1606_, v_inst_1607_, v_toBind_1608_, v___f_1609_, v_toApplicative_1610_, v_____do__lift_277__boxed_1612_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg(lean_object* v_inst_1614_, lean_object* v_initialMask_1615_, lean_object* v_test_1616_, lean_object* v_maxCalls_1617_){
_start:
{
lean_object* v_toApplicative_1618_; lean_object* v_toBind_1619_; lean_object* v___f_1620_; lean_object* v___f_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_toApplicative_1618_ = lean_ctor_get(v_inst_1614_, 0);
lean_inc_ref_n(v_toApplicative_1618_, 2);
v_toBind_1619_ = lean_ctor_get(v_inst_1614_, 1);
lean_inc_n(v_toBind_1619_, 2);
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1620_, 0, v_toApplicative_1618_);
lean_inc(v_test_1616_);
lean_inc_ref(v_initialMask_1615_);
v___f_1621_ = lean_alloc_closure((void*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1621_, 0, v_initialMask_1615_);
lean_closure_set(v___f_1621_, 1, v_test_1616_);
lean_closure_set(v___f_1621_, 2, v_maxCalls_1617_);
lean_closure_set(v___f_1621_, 3, v_inst_1614_);
lean_closure_set(v___f_1621_, 4, v_toBind_1619_);
lean_closure_set(v___f_1621_, 5, v___f_1620_);
lean_closure_set(v___f_1621_, 6, v_toApplicative_1618_);
v___x_1622_ = lean_apply_1(v_test_1616_, v_initialMask_1615_);
v___x_1623_ = lean_apply_4(v_toBind_1619_, lean_box(0), lean_box(0), v___x_1622_, v___f_1621_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search(lean_object* v_m_1624_, lean_object* v_inst_1625_, lean_object* v_initialMask_1626_, lean_object* v_test_1627_, lean_object* v_maxCalls_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_Util_ParamMinimizer_search___redArg(v_inst_1625_, v_initialMask_1626_, v_test_1627_, v_maxCalls_1628_);
return v___x_1629_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_ParamMinimizer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Util_ParamMinimizer_instInhabitedStatus_default = _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus_default();
l_Lean_Util_ParamMinimizer_instInhabitedStatus = _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_ParamMinimizer(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ParamMinimizer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ParamMinimizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_ParamMinimizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_ParamMinimizer(builtin);
}
#ifdef __cplusplus
}
#endif
