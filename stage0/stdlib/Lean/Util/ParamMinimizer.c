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
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_x_171__boxed_114_; lean_object* v_res_115_; 
v_x_171__boxed_114_ = lean_unbox(v_x_112_);
v_res_115_ = l_Lean_Util_ParamMinimizer_instReprStatus_repr(v_x_171__boxed_114_, v_prec_113_);
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
uint8_t v___x_6886__boxed_389_; lean_object* v_res_390_; 
v___x_6886__boxed_389_ = lean_unbox(v___x_387_);
v_res_390_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(v_toPure_386_, v___x_6886__boxed_389_, v_____x_388_);
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
lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_621_; 
v_fst_570_ = lean_ctor_get(v_____x_569_, 0);
v_snd_571_ = lean_ctor_get(v_____x_569_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v_____x_569_);
if (v_isSharedCheck_621_ == 0)
{
v___x_573_ = v_____x_569_;
v_isShared_574_ = v_isSharedCheck_621_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_snd_571_);
lean_inc(v_fst_570_);
lean_dec(v_____x_569_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_621_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
if (lean_obj_tag(v_fst_570_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_612_; 
lean_del_object(v___x_573_);
lean_dec(v_toBind_566_);
lean_dec_ref(v_inst_565_);
v_a_603_ = lean_ctor_get(v_fst_570_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v_fst_570_);
if (v_isSharedCheck_612_ == 0)
{
v___x_605_ = v_fst_570_;
v_isShared_606_ = v_isSharedCheck_612_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v_fst_570_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_612_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_611_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v_snd_571_);
v___x_610_ = lean_apply_2(v_toPure_564_, lean_box(0), v___x_609_);
return v___x_610_;
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v_a_613_ = lean_ctor_get(v_fst_570_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v_fst_570_, 1);
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_nat_dec_lt(v___x_614_, v_maxCalls_568_);
if (v___x_615_ == 0)
{
lean_dec(v_a_613_);
goto v___jp_575_;
}
else
{
lean_object* v_numCalls_616_; uint8_t v___x_617_; 
v_numCalls_616_ = lean_ctor_get(v_a_613_, 2);
lean_inc(v_numCalls_616_);
lean_dec(v_a_613_);
v___x_617_ = lean_nat_dec_le(v_maxCalls_568_, v_numCalls_616_);
lean_dec(v_numCalls_616_);
if (v___x_617_ == 0)
{
goto v___jp_575_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_del_object(v___x_573_);
lean_dec(v_toBind_566_);
lean_dec_ref(v_inst_565_);
v___x_618_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0));
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v_snd_571_);
v___x_620_ = lean_apply_2(v_toPure_564_, lean_box(0), v___x_619_);
return v___x_620_;
}
}
}
v___jp_575_:
{
lean_object* v_cur_576_; lean_object* v_added_577_; lean_object* v_numCalls_578_; uint8_t v_found_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_602_; 
v_cur_576_ = lean_ctor_get(v_snd_571_, 0);
v_added_577_ = lean_ctor_get(v_snd_571_, 1);
v_numCalls_578_ = lean_ctor_get(v_snd_571_, 2);
v_found_579_ = lean_ctor_get_uint8(v_snd_571_, sizeof(void*)*3);
v_isSharedCheck_602_ = !lean_is_exclusive(v_snd_571_);
if (v_isSharedCheck_602_ == 0)
{
v___x_581_ = v_snd_571_;
v_isShared_582_ = v_isSharedCheck_602_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_numCalls_578_);
lean_inc(v_added_577_);
lean_inc(v_cur_576_);
lean_dec(v_snd_571_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_602_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_583_ = 1;
v___x_584_ = lean_box(v___x_583_);
lean_inc_n(v_toPure_564_, 5);
v___f_585_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_585_, 0, v_toPure_564_);
lean_closure_set(v___f_585_, 1, v___x_584_);
lean_inc_n(v_toBind_566_, 3);
v___f_586_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1), 5, 4);
lean_closure_set(v___f_586_, 0, v_toPure_564_);
lean_closure_set(v___f_586_, 1, v_inst_565_);
lean_closure_set(v___f_586_, 2, v_toBind_566_);
lean_closure_set(v___f_586_, 3, v___f_585_);
v___f_587_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6), 4, 3);
lean_closure_set(v___f_587_, 0, v_toPure_564_);
lean_closure_set(v___f_587_, 1, v_toBind_566_);
lean_closure_set(v___f_587_, 2, v___f_586_);
lean_inc_ref(v_a_567_);
v___f_588_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7___boxed), 5, 4);
lean_closure_set(v___f_588_, 0, v_toPure_564_);
lean_closure_set(v___f_588_, 1, v_a_567_);
lean_closure_set(v___f_588_, 2, v_toBind_566_);
lean_closure_set(v___f_588_, 3, v___f_587_);
v___f_589_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_589_, 0, v_toPure_564_);
v___x_590_ = lean_box(0);
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_nat_add(v_numCalls_578_, v___x_591_);
lean_dec(v_numCalls_578_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 2, v___x_592_);
v___x_594_ = v___x_581_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_cur_576_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_added_577_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v___x_592_);
lean_ctor_set_uint8(v_reuseFailAlloc_601_, sizeof(void*)*3, v_found_579_);
v___x_594_ = v_reuseFailAlloc_601_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_596_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v___x_594_);
lean_ctor_set(v___x_573_, 0, v___x_590_);
v___x_596_ = v___x_573_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_594_);
v___x_596_ = v_reuseFailAlloc_600_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = lean_apply_2(v_toPure_564_, lean_box(0), v___x_596_);
lean_inc(v_toBind_566_);
v___x_598_ = lean_apply_4(v_toBind_566_, lean_box(0), lean_box(0), v___x_597_, v___f_589_);
v___x_599_ = lean_apply_4(v_toBind_566_, lean_box(0), lean_box(0), v___x_598_, v___f_588_);
return v___x_599_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed(lean_object* v_toPure_622_, lean_object* v_inst_623_, lean_object* v_toBind_624_, lean_object* v_a_625_, lean_object* v_maxCalls_626_, lean_object* v_____x_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(v_toPure_622_, v_inst_623_, v_toBind_624_, v_a_625_, v_maxCalls_626_, v_____x_627_);
lean_dec(v_maxCalls_626_);
lean_dec_ref(v_a_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(lean_object* v_toPure_629_, lean_object* v_inst_630_, lean_object* v_toBind_631_, lean_object* v_a_632_, lean_object* v_____x_633_){
_start:
{
lean_object* v_fst_634_; 
v_fst_634_ = lean_ctor_get(v_____x_633_, 0);
lean_inc(v_fst_634_);
if (lean_obj_tag(v_fst_634_) == 0)
{
lean_object* v_snd_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_651_; 
lean_dec(v_toBind_631_);
lean_dec_ref(v_inst_630_);
v_snd_635_ = lean_ctor_get(v_____x_633_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_____x_633_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v_____x_633_, 0);
lean_dec(v_unused_652_);
v___x_637_ = v_____x_633_;
v_isShared_638_ = v_isSharedCheck_651_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_snd_635_);
lean_dec(v_____x_633_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_651_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_650_; 
v_a_639_ = lean_ctor_get(v_fst_634_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_fst_634_);
if (v_isSharedCheck_650_ == 0)
{
v___x_641_ = v_fst_634_;
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v_fst_634_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_649_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_646_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_644_);
v___x_646_ = v___x_637_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_snd_635_);
v___x_646_ = v_reuseFailAlloc_648_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; 
v___x_647_ = lean_apply_2(v_toPure_629_, lean_box(0), v___x_646_);
return v___x_647_;
}
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v_snd_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_667_; 
v_a_653_ = lean_ctor_get(v_fst_634_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v_fst_634_, 1);
v_snd_654_ = lean_ctor_get(v_____x_633_, 1);
v_isSharedCheck_667_ = !lean_is_exclusive(v_____x_633_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; 
v_unused_668_ = lean_ctor_get(v_____x_633_, 0);
lean_dec(v_unused_668_);
v___x_656_ = v_____x_633_;
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_snd_654_);
lean_dec(v_____x_633_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_maxCalls_658_; lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___x_662_; 
v_maxCalls_658_ = lean_ctor_get(v_a_653_, 2);
lean_inc(v_maxCalls_658_);
lean_dec(v_a_653_);
lean_inc_ref(v_a_632_);
lean_inc(v_toBind_631_);
lean_inc_n(v_toPure_629_, 2);
v___f_659_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_659_, 0, v_toPure_629_);
lean_closure_set(v___f_659_, 1, v_inst_630_);
lean_closure_set(v___f_659_, 2, v_toBind_631_);
lean_closure_set(v___f_659_, 3, v_a_632_);
lean_closure_set(v___f_659_, 4, v_maxCalls_658_);
v___f_660_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_660_, 0, v_toPure_629_);
lean_inc(v_snd_654_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v_snd_654_);
v___x_662_ = v___x_656_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_snd_654_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_snd_654_);
v___x_662_ = v_reuseFailAlloc_666_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = lean_apply_2(v_toPure_629_, lean_box(0), v___x_662_);
lean_inc(v_toBind_631_);
v___x_664_ = lean_apply_4(v_toBind_631_, lean_box(0), lean_box(0), v___x_663_, v___f_660_);
v___x_665_ = lean_apply_4(v_toBind_631_, lean_box(0), lean_box(0), v___x_664_, v___f_659_);
return v___x_665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed(lean_object* v_toPure_669_, lean_object* v_inst_670_, lean_object* v_toBind_671_, lean_object* v_a_672_, lean_object* v_____x_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(v_toPure_669_, v_inst_670_, v_toBind_671_, v_a_672_, v_____x_673_);
lean_dec_ref(v_a_672_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(lean_object* v_inst_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_toApplicative_678_; lean_object* v_toBind_679_; lean_object* v_toPure_680_; lean_object* v___f_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_toApplicative_678_ = lean_ctor_get(v_inst_675_, 0);
v_toBind_679_ = lean_ctor_get(v_inst_675_, 1);
lean_inc_n(v_toBind_679_, 2);
v_toPure_680_ = lean_ctor_get(v_toApplicative_678_, 1);
lean_inc_n(v_toPure_680_, 2);
lean_inc_ref_n(v_a_676_, 2);
v___f_681_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_681_, 0, v_toPure_680_);
lean_closure_set(v___f_681_, 1, v_inst_675_);
lean_closure_set(v___f_681_, 2, v_toBind_679_);
lean_closure_set(v___f_681_, 3, v_a_676_);
v___x_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_682_, 0, v_a_676_);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v_a_677_);
v___x_684_ = lean_apply_2(v_toPure_680_, lean_box(0), v___x_683_);
v___x_685_ = lean_apply_4(v_toBind_679_, lean_box(0), lean_box(0), v___x_684_, v___f_681_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___boxed(lean_object* v_inst_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_686_, v_a_687_, v_a_688_);
lean_dec_ref(v_a_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(lean_object* v_m_690_, lean_object* v_inst_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_691_, v_a_692_, v_a_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___boxed(lean_object* v_m_695_, lean_object* v_inst_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(v_m_695_, v_inst_696_, v_a_697_, v_a_698_);
lean_dec_ref(v_a_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0(lean_object* v_toPure_700_, lean_object* v_____x_701_){
_start:
{
lean_object* v_fst_702_; 
v_fst_702_ = lean_ctor_get(v_____x_701_, 0);
lean_inc(v_fst_702_);
if (lean_obj_tag(v_fst_702_) == 0)
{
lean_object* v_snd_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_719_; 
v_snd_703_ = lean_ctor_get(v_____x_701_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_____x_701_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v_____x_701_, 0);
lean_dec(v_unused_720_);
v___x_705_ = v_____x_701_;
v_isShared_706_ = v_isSharedCheck_719_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_snd_703_);
lean_dec(v_____x_701_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_719_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_718_; 
v_a_707_ = lean_ctor_get(v_fst_702_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v_fst_702_);
if (v_isSharedCheck_718_ == 0)
{
v___x_709_ = v_fst_702_;
v_isShared_710_ = v_isSharedCheck_718_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v_fst_702_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_718_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_717_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_712_);
v___x_714_ = v___x_705_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_snd_703_);
v___x_714_ = v_reuseFailAlloc_716_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; 
v___x_715_ = lean_apply_2(v_toPure_700_, lean_box(0), v___x_714_);
return v___x_715_;
}
}
}
}
}
else
{
lean_object* v_snd_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_737_; 
v_snd_721_ = lean_ctor_get(v_____x_701_, 1);
v_isSharedCheck_737_ = !lean_is_exclusive(v_____x_701_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v_____x_701_, 0);
lean_dec(v_unused_738_);
v___x_723_ = v_____x_701_;
v_isShared_724_ = v_isSharedCheck_737_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_snd_721_);
lean_dec(v_____x_701_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_737_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_736_; 
v_a_725_ = lean_ctor_get(v_fst_702_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_fst_702_);
if (v_isSharedCheck_736_ == 0)
{
v___x_727_ = v_fst_702_;
v_isShared_728_ = v_isSharedCheck_736_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v_fst_702_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_736_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_735_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_732_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_730_);
v___x_732_ = v___x_723_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_snd_721_);
v___x_732_ = v_reuseFailAlloc_734_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; 
v___x_733_ = lean_apply_2(v_toPure_700_, lean_box(0), v___x_732_);
return v___x_733_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1(lean_object* v_toPure_739_, lean_object* v___x_740_, lean_object* v_____x_741_){
_start:
{
lean_object* v_fst_742_; 
v_fst_742_ = lean_ctor_get(v_____x_741_, 0);
lean_inc(v_fst_742_);
if (lean_obj_tag(v_fst_742_) == 0)
{
lean_object* v_snd_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_759_; 
v_snd_743_ = lean_ctor_get(v_____x_741_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_____x_741_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v_____x_741_, 0);
lean_dec(v_unused_760_);
v___x_745_ = v_____x_741_;
v_isShared_746_ = v_isSharedCheck_759_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_snd_743_);
lean_dec(v_____x_741_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_759_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_758_; 
v_a_747_ = lean_ctor_get(v_fst_742_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v_fst_742_);
if (v_isSharedCheck_758_ == 0)
{
v___x_749_ = v_fst_742_;
v_isShared_750_ = v_isSharedCheck_758_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v_fst_742_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_758_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_757_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_752_);
v___x_754_ = v___x_745_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_snd_743_);
v___x_754_ = v_reuseFailAlloc_756_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; 
v___x_755_ = lean_apply_2(v_toPure_739_, lean_box(0), v___x_754_);
return v___x_755_;
}
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_788_; 
v_a_761_ = lean_ctor_get(v_fst_742_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_fst_742_);
if (v_isSharedCheck_788_ == 0)
{
v___x_763_ = v_fst_742_;
v_isShared_764_ = v_isSharedCheck_788_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v_fst_742_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_788_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v_fst_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_786_; 
v_fst_765_ = lean_ctor_get(v_a_761_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v_a_761_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v_a_761_, 1);
lean_dec(v_unused_787_);
v___x_767_ = v_a_761_;
v_isShared_768_ = v_isSharedCheck_786_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_fst_765_);
lean_dec(v_a_761_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_786_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
if (lean_obj_tag(v_fst_765_) == 0)
{
lean_object* v_snd_769_; lean_object* v___x_771_; 
v_snd_769_ = lean_ctor_get(v_____x_741_, 1);
lean_inc(v_snd_769_);
lean_dec_ref(v_____x_741_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_740_);
v___x_771_ = v___x_763_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_740_);
v___x_771_ = v_reuseFailAlloc_776_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v_snd_769_);
lean_ctor_set(v___x_767_, 0, v___x_771_);
v___x_773_ = v___x_767_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_snd_769_);
v___x_773_ = v_reuseFailAlloc_775_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; 
v___x_774_ = lean_apply_2(v_toPure_739_, lean_box(0), v___x_773_);
return v___x_774_;
}
}
}
else
{
lean_object* v_snd_777_; lean_object* v_val_778_; lean_object* v___x_780_; 
v_snd_777_ = lean_ctor_get(v_____x_741_, 1);
lean_inc(v_snd_777_);
lean_dec_ref(v_____x_741_);
v_val_778_ = lean_ctor_get(v_fst_765_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v_fst_765_, 1);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v_val_778_);
v___x_780_ = v___x_763_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_val_778_);
v___x_780_ = v_reuseFailAlloc_785_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v_snd_777_);
lean_ctor_set(v___x_767_, 0, v___x_780_);
v___x_782_ = v___x_767_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_snd_777_);
v___x_782_ = v_reuseFailAlloc_784_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; 
v___x_783_ = lean_apply_2(v_toPure_739_, lean_box(0), v___x_782_);
return v___x_783_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2(lean_object* v_toPure_789_, lean_object* v___x_790_, lean_object* v___x_791_, lean_object* v_____x_792_){
_start:
{
lean_object* v_fst_793_; 
v_fst_793_ = lean_ctor_get(v_____x_792_, 0);
lean_inc(v_fst_793_);
if (lean_obj_tag(v_fst_793_) == 0)
{
lean_object* v_snd_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_810_; 
lean_dec_ref(v___x_790_);
v_snd_794_ = lean_ctor_get(v_____x_792_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v_____x_792_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v_____x_792_, 0);
lean_dec(v_unused_811_);
v___x_796_ = v_____x_792_;
v_isShared_797_ = v_isSharedCheck_810_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_snd_794_);
lean_dec(v_____x_792_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_810_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_809_; 
v_a_798_ = lean_ctor_get(v_fst_793_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v_fst_793_);
if (v_isSharedCheck_809_ == 0)
{
v___x_800_ = v_fst_793_;
v_isShared_801_ = v_isSharedCheck_809_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v_fst_793_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_809_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_808_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_803_);
v___x_805_ = v___x_796_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_snd_794_);
v___x_805_ = v_reuseFailAlloc_807_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; 
v___x_806_ = lean_apply_2(v_toPure_789_, lean_box(0), v___x_805_);
return v___x_806_;
}
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_847_; 
v_a_812_ = lean_ctor_get(v_fst_793_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v_fst_793_);
if (v_isSharedCheck_847_ == 0)
{
v___x_814_ = v_fst_793_;
v_isShared_815_ = v_isSharedCheck_847_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v_fst_793_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_847_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
uint8_t v___x_816_; 
v___x_816_ = lean_unbox(v_a_812_);
lean_dec(v_a_812_);
if (v___x_816_ == 0)
{
lean_object* v_snd_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_829_; 
v_snd_817_ = lean_ctor_get(v_____x_792_, 1);
v_isSharedCheck_829_ = !lean_is_exclusive(v_____x_792_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v_____x_792_, 0);
lean_dec(v_unused_830_);
v___x_819_ = v_____x_792_;
v_isShared_820_ = v_isSharedCheck_829_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_snd_817_);
lean_dec(v_____x_792_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_829_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_790_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_821_);
v___x_823_ = v___x_814_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_828_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_825_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_823_);
v___x_825_ = v___x_819_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_snd_817_);
v___x_825_ = v_reuseFailAlloc_827_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_826_; 
v___x_826_ = lean_apply_2(v_toPure_789_, lean_box(0), v___x_825_);
return v___x_826_;
}
}
}
}
else
{
lean_object* v_snd_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_845_; 
lean_dec_ref(v___x_790_);
v_snd_831_ = lean_ctor_get(v_____x_792_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_____x_792_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; 
v_unused_846_ = lean_ctor_get(v_____x_792_, 0);
lean_dec(v_unused_846_);
v___x_833_ = v_____x_792_;
v_isShared_834_ = v_isSharedCheck_845_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_snd_831_);
lean_dec(v_____x_792_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_845_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_791_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v___x_791_);
lean_ctor_set(v___x_833_, 0, v___x_835_);
v___x_837_ = v___x_833_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_791_);
v___x_837_ = v_reuseFailAlloc_844_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_838_);
v___x_840_ = v___x_814_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_843_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v_snd_831_);
v___x_842_ = lean_apply_2(v_toPure_789_, lean_box(0), v___x_841_);
return v___x_842_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(lean_object* v_inst_848_, lean_object* v_toBind_849_, lean_object* v___f_850_, lean_object* v_____r_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_848_, v___y_852_, v___y_853_);
v___x_855_ = lean_apply_4(v_toBind_849_, lean_box(0), lean_box(0), v___x_854_, v___f_850_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed(lean_object* v_inst_856_, lean_object* v_toBind_857_, lean_object* v___f_858_, lean_object* v_____r_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(v_inst_856_, v_toBind_857_, v___f_858_, v_____r_859_, v___y_860_, v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(lean_object* v_toPure_863_, lean_object* v_next_864_, lean_object* v_G_865_, lean_object* v___y_866_, lean_object* v_____x_867_){
_start:
{
lean_object* v_fst_868_; 
v_fst_868_ = lean_ctor_get(v_____x_867_, 0);
lean_inc(v_fst_868_);
if (lean_obj_tag(v_fst_868_) == 0)
{
lean_object* v_snd_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_885_; 
lean_dec(v_G_865_);
v_snd_869_ = lean_ctor_get(v_____x_867_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_____x_867_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v_____x_867_, 0);
lean_dec(v_unused_886_);
v___x_871_ = v_____x_867_;
v_isShared_872_ = v_isSharedCheck_885_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_snd_869_);
lean_dec(v_____x_867_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_885_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_884_; 
v_a_873_ = lean_ctor_get(v_fst_868_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v_fst_868_);
if (v_isSharedCheck_884_ == 0)
{
v___x_875_ = v_fst_868_;
v_isShared_876_ = v_isSharedCheck_884_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v_fst_868_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_884_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_883_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_878_);
v___x_880_ = v___x_871_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_snd_869_);
v___x_880_ = v_reuseFailAlloc_882_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; 
v___x_881_ = lean_apply_2(v_toPure_863_, lean_box(0), v___x_880_);
return v___x_881_;
}
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_910_; 
v_a_887_ = lean_ctor_get(v_fst_868_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v_fst_868_);
if (v_isSharedCheck_910_ == 0)
{
v___x_889_ = v_fst_868_;
v_isShared_890_ = v_isSharedCheck_910_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v_fst_868_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_910_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
if (lean_obj_tag(v_a_887_) == 0)
{
lean_object* v_snd_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_903_; 
lean_dec(v_G_865_);
v_snd_891_ = lean_ctor_get(v_____x_867_, 1);
v_isSharedCheck_903_ = !lean_is_exclusive(v_____x_867_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; 
v_unused_904_ = lean_ctor_get(v_____x_867_, 0);
lean_dec(v_unused_904_);
v___x_893_ = v_____x_867_;
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_snd_891_);
lean_dec(v_____x_867_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v_a_895_; lean_object* v___x_897_; 
v_a_895_ = lean_ctor_get(v_a_887_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v_a_887_, 1);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v_a_895_);
v___x_897_ = v___x_889_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_895_);
v___x_897_ = v_reuseFailAlloc_902_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_897_);
v___x_899_ = v___x_893_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_snd_891_);
v___x_899_ = v_reuseFailAlloc_901_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; 
v___x_900_ = lean_apply_2(v_toPure_863_, lean_box(0), v___x_899_);
return v___x_900_;
}
}
}
}
else
{
lean_object* v_snd_905_; lean_object* v_a_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
lean_del_object(v___x_889_);
lean_dec(v_toPure_863_);
v_snd_905_ = lean_ctor_get(v_____x_867_, 1);
lean_inc(v_snd_905_);
lean_dec_ref(v_____x_867_);
v_a_906_ = lean_ctor_get(v_a_887_, 0);
lean_inc(v_a_906_);
lean_dec_ref_known(v_a_887_, 1);
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_nat_add(v_next_864_, v___x_907_);
lean_inc_ref(v___y_866_);
v___x_909_ = lean_apply_6(v_G_865_, v___x_908_, v_a_906_, lean_box(0), lean_box(0), v___y_866_, v_snd_905_);
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed(lean_object* v_toPure_911_, lean_object* v_next_912_, lean_object* v_G_913_, lean_object* v___y_914_, lean_object* v_____x_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(v_toPure_911_, v_next_912_, v_G_913_, v___y_914_, v_____x_915_);
lean_dec_ref(v___y_914_);
lean_dec(v_next_912_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(lean_object* v_toPure_917_, lean_object* v___f_918_, lean_object* v___y_919_, lean_object* v_____x_920_){
_start:
{
lean_object* v_fst_921_; 
v_fst_921_ = lean_ctor_get(v_____x_920_, 0);
lean_inc(v_fst_921_);
if (lean_obj_tag(v_fst_921_) == 0)
{
lean_object* v_snd_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_938_; 
lean_dec(v___f_918_);
v_snd_922_ = lean_ctor_get(v_____x_920_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v_____x_920_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v_____x_920_, 0);
lean_dec(v_unused_939_);
v___x_924_ = v_____x_920_;
v_isShared_925_ = v_isSharedCheck_938_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_snd_922_);
lean_dec(v_____x_920_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_938_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_937_; 
v_a_926_ = lean_ctor_get(v_fst_921_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v_fst_921_);
if (v_isSharedCheck_937_ == 0)
{
v___x_928_ = v_fst_921_;
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v_fst_921_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_936_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_933_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_931_);
v___x_933_ = v___x_924_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_snd_922_);
v___x_933_ = v_reuseFailAlloc_935_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; 
v___x_934_ = lean_apply_2(v_toPure_917_, lean_box(0), v___x_933_);
return v___x_934_;
}
}
}
}
}
else
{
lean_object* v_snd_940_; lean_object* v_a_941_; lean_object* v___x_942_; 
lean_dec(v_toPure_917_);
v_snd_940_ = lean_ctor_get(v_____x_920_, 1);
lean_inc(v_snd_940_);
lean_dec_ref(v_____x_920_);
v_a_941_ = lean_ctor_get(v_fst_921_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v_fst_921_, 1);
lean_inc_ref(v___y_919_);
v___x_942_ = lean_apply_3(v___f_918_, v_a_941_, v___y_919_, v_snd_940_);
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed(lean_object* v_toPure_943_, lean_object* v___f_944_, lean_object* v___y_945_, lean_object* v_____x_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(v_toPure_943_, v___f_944_, v___y_945_, v_____x_946_);
lean_dec_ref(v___y_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(lean_object* v___x_948_, lean_object* v_toPure_949_, lean_object* v_toBind_950_, lean_object* v___f_951_, lean_object* v_initialMask_952_, lean_object* v___f_953_, lean_object* v_inst_954_, lean_object* v___x_955_, lean_object* v_next_956_, lean_object* v_acc_957_, lean_object* v_h_958_, lean_object* v_G_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
uint8_t v___x_962_; 
v___x_962_ = lean_nat_dec_lt(v_next_956_, v___x_948_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec(v_G_959_);
lean_dec(v_next_956_);
lean_dec_ref(v_inst_954_);
lean_dec(v___f_953_);
lean_dec(v___f_951_);
lean_dec(v_toBind_950_);
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v_acc_957_);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___y_961_);
v___x_965_ = lean_apply_2(v_toPure_949_, lean_box(0), v___x_964_);
return v___x_965_;
}
else
{
lean_object* v___f_966_; lean_object* v___y_968_; lean_object* v___x_971_; uint8_t v___x_972_; 
lean_dec_ref(v_acc_957_);
lean_inc_ref(v___y_960_);
lean_inc(v_next_956_);
lean_inc(v_toPure_949_);
v___f_966_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_966_, 0, v_toPure_949_);
lean_closure_set(v___f_966_, 1, v_next_956_);
lean_closure_set(v___f_966_, 2, v_G_959_);
lean_closure_set(v___f_966_, 3, v___y_960_);
v___x_971_ = lean_array_fget_borrowed(v_initialMask_952_, v_next_956_);
v___x_972_ = lean_unbox(v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___f_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_inc_ref(v___y_960_);
v___f_973_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_973_, 0, v_toPure_949_);
lean_closure_set(v___f_973_, 1, v___f_953_);
lean_closure_set(v___f_973_, 2, v___y_960_);
v___x_974_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(v_next_956_, v_inst_954_, v___y_961_);
lean_inc(v_toBind_950_);
v___x_975_ = lean_apply_4(v_toBind_950_, lean_box(0), lean_box(0), v___x_974_, v___f_973_);
v___y_968_ = v___x_975_;
goto v___jp_967_;
}
else
{
lean_object* v___x_976_; 
lean_dec(v_next_956_);
lean_dec_ref(v_inst_954_);
lean_dec(v_toPure_949_);
lean_inc_ref(v___y_960_);
v___x_976_ = lean_apply_3(v___f_953_, v___x_955_, v___y_960_, v___y_961_);
v___y_968_ = v___x_976_;
goto v___jp_967_;
}
v___jp_967_:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
lean_inc(v_toBind_950_);
v___x_969_ = lean_apply_4(v_toBind_950_, lean_box(0), lean_box(0), v___y_968_, v___f_951_);
v___x_970_ = lean_apply_4(v_toBind_950_, lean_box(0), lean_box(0), v___x_969_, v___f_966_);
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed(lean_object* v___x_977_, lean_object* v_toPure_978_, lean_object* v_toBind_979_, lean_object* v___f_980_, lean_object* v_initialMask_981_, lean_object* v___f_982_, lean_object* v_inst_983_, lean_object* v___x_984_, lean_object* v_next_985_, lean_object* v_acc_986_, lean_object* v_h_987_, lean_object* v_G_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(v___x_977_, v_toPure_978_, v_toBind_979_, v___f_980_, v_initialMask_981_, v___f_982_, v_inst_983_, v___x_984_, v_next_985_, v_acc_986_, v_h_987_, v_G_988_, v___y_989_, v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec_ref(v_initialMask_981_);
lean_dec(v___x_977_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(lean_object* v_toPure_995_, lean_object* v_inst_996_, lean_object* v_toBind_997_, lean_object* v___f_998_, lean_object* v_a_999_, lean_object* v_____x_1000_){
_start:
{
lean_object* v_fst_1001_; 
v_fst_1001_ = lean_ctor_get(v_____x_1000_, 0);
lean_inc(v_fst_1001_);
if (lean_obj_tag(v_fst_1001_) == 0)
{
lean_object* v_snd_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v___f_998_);
lean_dec(v_toBind_997_);
lean_dec_ref(v_inst_996_);
v_snd_1002_ = lean_ctor_get(v_____x_1000_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_____x_1000_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v_____x_1000_, 0);
lean_dec(v_unused_1019_);
v___x_1004_ = v_____x_1000_;
v_isShared_1005_ = v_isSharedCheck_1018_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_snd_1002_);
lean_dec(v_____x_1000_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1018_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1017_; 
v_a_1006_ = lean_ctor_get(v_fst_1001_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_fst_1001_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1008_ = v_fst_1001_;
v_isShared_1009_ = v_isSharedCheck_1017_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v_fst_1001_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1017_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1013_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1011_);
v___x_1013_ = v___x_1004_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_snd_1002_);
v___x_1013_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_apply_2(v_toPure_995_, lean_box(0), v___x_1013_);
return v___x_1014_;
}
}
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v_snd_1021_; lean_object* v_initialMask_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___f_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___x_6128__overap_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_a_1020_ = lean_ctor_get(v_fst_1001_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v_fst_1001_, 1);
v_snd_1021_ = lean_ctor_get(v_____x_1000_, 1);
lean_inc(v_snd_1021_);
lean_dec_ref(v_____x_1000_);
v_initialMask_1022_ = lean_ctor_get(v_a_1020_, 0);
lean_inc_ref(v_initialMask_1022_);
lean_dec(v_a_1020_);
v___x_1023_ = lean_array_get_size(v_initialMask_1022_);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_box(0);
lean_inc_n(v_toPure_995_, 2);
v___f_1026_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1026_, 0, v_toPure_995_);
lean_closure_set(v___f_1026_, 1, v___x_1025_);
v___x_1027_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0));
v___f_1028_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1028_, 0, v_toPure_995_);
lean_closure_set(v___f_1028_, 1, v___x_1027_);
lean_closure_set(v___f_1028_, 2, v___x_1025_);
lean_inc_n(v_toBind_997_, 2);
lean_inc_ref(v_inst_996_);
v___f_1029_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1029_, 0, v_inst_996_);
lean_closure_set(v___f_1029_, 1, v_toBind_997_);
lean_closure_set(v___f_1029_, 2, v___f_1028_);
v___f_1030_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed), 14, 8);
lean_closure_set(v___f_1030_, 0, v___x_1023_);
lean_closure_set(v___f_1030_, 1, v_toPure_995_);
lean_closure_set(v___f_1030_, 2, v_toBind_997_);
lean_closure_set(v___f_1030_, 3, v___f_998_);
lean_closure_set(v___f_1030_, 4, v_initialMask_1022_);
lean_closure_set(v___f_1030_, 5, v___f_1029_);
lean_closure_set(v___f_1030_, 6, v_inst_996_);
lean_closure_set(v___f_1030_, 7, v___x_1025_);
v___x_6128__overap_1031_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1030_, v___x_1024_, v___x_1027_, lean_box(0));
lean_inc_ref(v_a_999_);
v___x_1032_ = lean_apply_2(v___x_6128__overap_1031_, v_a_999_, v_snd_1021_);
v___x_1033_ = lean_apply_4(v_toBind_997_, lean_box(0), lean_box(0), v___x_1032_, v___f_1026_);
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed(lean_object* v_toPure_1034_, lean_object* v_inst_1035_, lean_object* v_toBind_1036_, lean_object* v___f_1037_, lean_object* v_a_1038_, lean_object* v_____x_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(v_toPure_1034_, v_inst_1035_, v_toBind_1036_, v___f_1037_, v_a_1038_, v_____x_1039_);
lean_dec_ref(v_a_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(lean_object* v_inst_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_toApplicative_1044_; lean_object* v_toBind_1045_; lean_object* v_toPure_1046_; lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_toApplicative_1044_ = lean_ctor_get(v_inst_1041_, 0);
v_toBind_1045_ = lean_ctor_get(v_inst_1041_, 1);
lean_inc_n(v_toBind_1045_, 2);
v_toPure_1046_ = lean_ctor_get(v_toApplicative_1044_, 1);
lean_inc_n(v_toPure_1046_, 3);
v___f_1047_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1047_, 0, v_toPure_1046_);
lean_inc_ref_n(v_a_1042_, 2);
v___f_1048_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_1048_, 0, v_toPure_1046_);
lean_closure_set(v___f_1048_, 1, v_inst_1041_);
lean_closure_set(v___f_1048_, 2, v_toBind_1045_);
lean_closure_set(v___f_1048_, 3, v___f_1047_);
lean_closure_set(v___f_1048_, 4, v_a_1042_);
v___x_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_a_1042_);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_a_1043_);
v___x_1051_ = lean_apply_2(v_toPure_1046_, lean_box(0), v___x_1050_);
v___x_1052_ = lean_apply_4(v_toBind_1045_, lean_box(0), lean_box(0), v___x_1051_, v___f_1048_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___boxed(lean_object* v_inst_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v_a_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(lean_object* v_m_1057_, lean_object* v_inst_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1058_, v_a_1059_, v_a_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___boxed(lean_object* v_m_1062_, lean_object* v_inst_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(v_m_1062_, v_inst_1063_, v_a_1064_, v_a_1065_);
lean_dec_ref(v_a_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0(lean_object* v_toPure_1069_, lean_object* v_____x_1070_){
_start:
{
lean_object* v_fst_1071_; 
v_fst_1071_ = lean_ctor_get(v_____x_1070_, 0);
lean_inc(v_fst_1071_);
if (lean_obj_tag(v_fst_1071_) == 0)
{
lean_object* v_snd_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1088_; 
v_snd_1072_ = lean_ctor_get(v_____x_1070_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_____x_1070_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v_____x_1070_, 0);
lean_dec(v_unused_1089_);
v___x_1074_ = v_____x_1070_;
v_isShared_1075_ = v_isSharedCheck_1088_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_snd_1072_);
lean_dec(v_____x_1070_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1088_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1087_; 
v_a_1076_ = lean_ctor_get(v_fst_1071_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_fst_1071_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1078_ = v_fst_1071_;
v_isShared_1079_ = v_isSharedCheck_1087_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v_fst_1071_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1087_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1083_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1081_);
v___x_1083_ = v___x_1074_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_snd_1072_);
v___x_1083_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_apply_2(v_toPure_1069_, lean_box(0), v___x_1083_);
return v___x_1084_;
}
}
}
}
}
else
{
lean_object* v_snd_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref_known(v_fst_1071_, 1);
v_snd_1090_ = lean_ctor_get(v_____x_1070_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_____x_1070_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v_____x_1070_, 0);
lean_dec(v_unused_1100_);
v___x_1092_ = v_____x_1070_;
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_snd_1090_);
lean_dec(v_____x_1070_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0));
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1094_);
v___x_1096_ = v___x_1092_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_snd_1090_);
v___x_1096_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_apply_2(v_toPure_1069_, lean_box(0), v___x_1096_);
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1(lean_object* v_toPure_1101_, lean_object* v_____x_1102_){
_start:
{
lean_object* v_fst_1103_; 
v_fst_1103_ = lean_ctor_get(v_____x_1102_, 0);
lean_inc(v_fst_1103_);
if (lean_obj_tag(v_fst_1103_) == 0)
{
lean_object* v_snd_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1120_; 
v_snd_1104_ = lean_ctor_get(v_____x_1102_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_____x_1102_);
if (v_isSharedCheck_1120_ == 0)
{
lean_object* v_unused_1121_; 
v_unused_1121_ = lean_ctor_get(v_____x_1102_, 0);
lean_dec(v_unused_1121_);
v___x_1106_ = v_____x_1102_;
v_isShared_1107_ = v_isSharedCheck_1120_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_snd_1104_);
lean_dec(v_____x_1102_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1120_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1119_; 
v_a_1108_ = lean_ctor_get(v_fst_1103_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_fst_1103_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1110_ = v_fst_1103_;
v_isShared_1111_ = v_isSharedCheck_1119_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v_fst_1103_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1119_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1115_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1113_);
v___x_1115_ = v___x_1106_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_snd_1104_);
v___x_1115_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_apply_2(v_toPure_1101_, lean_box(0), v___x_1115_);
return v___x_1116_;
}
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1168_; 
v_a_1122_ = lean_ctor_get(v_fst_1103_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_fst_1103_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1124_ = v_fst_1103_;
v_isShared_1125_ = v_isSharedCheck_1168_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v_fst_1103_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1168_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
if (lean_obj_tag(v_a_1122_) == 0)
{
lean_object* v_snd_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1145_; 
v_snd_1126_ = lean_ctor_get(v_____x_1102_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_____x_1102_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; 
v_unused_1146_ = lean_ctor_get(v_____x_1102_, 0);
lean_dec(v_unused_1146_);
v___x_1128_ = v_____x_1102_;
v_isShared_1129_ = v_isSharedCheck_1145_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_snd_1126_);
lean_dec(v_____x_1102_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1145_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1144_; 
v_a_1130_ = lean_ctor_get(v_a_1122_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_a_1122_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1132_ = v_a_1122_;
v_isShared_1133_ = v_isSharedCheck_1144_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v_a_1122_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1144_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 1);
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1137_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1135_);
v___x_1137_ = v___x_1124_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1139_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1137_);
v___x_1139_ = v___x_1128_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_snd_1126_);
v___x_1139_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_apply_2(v_toPure_1101_, lean_box(0), v___x_1139_);
return v___x_1140_;
}
}
}
}
}
}
else
{
lean_object* v_snd_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1166_; 
v_snd_1147_ = lean_ctor_get(v_____x_1102_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_____x_1102_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; 
v_unused_1167_ = lean_ctor_get(v_____x_1102_, 0);
lean_dec(v_unused_1167_);
v___x_1149_ = v_____x_1102_;
v_isShared_1150_ = v_isSharedCheck_1166_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_snd_1147_);
lean_dec(v_____x_1102_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1166_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1165_; 
v_a_1151_ = lean_ctor_get(v_a_1122_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_a_1122_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1153_ = v_a_1122_;
v_isShared_1154_ = v_isSharedCheck_1165_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v_a_1122_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1165_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set_tag(v___x_1153_, 0);
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1158_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1156_);
v___x_1158_ = v___x_1124_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1160_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1158_);
v___x_1160_ = v___x_1149_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_snd_1147_);
v___x_1160_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_apply_2(v_toPure_1101_, lean_box(0), v___x_1160_);
return v___x_1161_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2(lean_object* v_toPure_1169_, lean_object* v___x_1170_, lean_object* v_____x_1171_){
_start:
{
lean_object* v_fst_1172_; 
v_fst_1172_ = lean_ctor_get(v_____x_1171_, 0);
lean_inc(v_fst_1172_);
if (lean_obj_tag(v_fst_1172_) == 0)
{
lean_object* v_snd_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1189_; 
lean_dec(v___x_1170_);
v_snd_1173_ = lean_ctor_get(v_____x_1171_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_____x_1171_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; 
v_unused_1190_ = lean_ctor_get(v_____x_1171_, 0);
lean_dec(v_unused_1190_);
v___x_1175_ = v_____x_1171_;
v_isShared_1176_ = v_isSharedCheck_1189_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_snd_1173_);
lean_dec(v_____x_1171_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1189_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1188_; 
v_a_1177_ = lean_ctor_get(v_fst_1172_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_fst_1172_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1179_ = v_fst_1172_;
v_isShared_1180_ = v_isSharedCheck_1188_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v_fst_1172_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1188_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1184_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1182_);
v___x_1184_ = v___x_1175_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_snd_1173_);
v___x_1184_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_apply_2(v_toPure_1169_, lean_box(0), v___x_1184_);
return v___x_1185_;
}
}
}
}
}
else
{
lean_object* v_snd_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1208_; 
v_snd_1191_ = lean_ctor_get(v_____x_1171_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_____x_1171_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v_____x_1171_, 0);
lean_dec(v_unused_1209_);
v___x_1193_ = v_____x_1171_;
v_isShared_1194_ = v_isSharedCheck_1208_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_snd_1191_);
lean_dec(v_____x_1171_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1208_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1206_; 
v_isSharedCheck_1206_ = !lean_is_exclusive(v_fst_1172_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; 
v_unused_1207_ = lean_ctor_get(v_fst_1172_, 0);
lean_dec(v_unused_1207_);
v___x_1196_ = v_fst_1172_;
v_isShared_1197_ = v_isSharedCheck_1206_;
goto v_resetjp_1195_;
}
else
{
lean_dec(v_fst_1172_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1206_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1170_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1198_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1200_);
v___x_1202_ = v___x_1193_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_snd_1191_);
v___x_1202_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_apply_2(v_toPure_1169_, lean_box(0), v___x_1202_);
return v___x_1203_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(lean_object* v_toPure_1210_, lean_object* v___x_1211_, lean_object* v_inst_1212_, lean_object* v_toBind_1213_, lean_object* v___f_1214_, lean_object* v___x_1215_, lean_object* v_____x_1216_){
_start:
{
lean_object* v_fst_1217_; 
v_fst_1217_ = lean_ctor_get(v_____x_1216_, 0);
lean_inc(v_fst_1217_);
if (lean_obj_tag(v_fst_1217_) == 0)
{
lean_object* v_snd_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v___x_1215_);
lean_dec(v___f_1214_);
lean_dec(v_toBind_1213_);
lean_dec_ref(v_inst_1212_);
v_snd_1218_ = lean_ctor_get(v_____x_1216_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_____x_1216_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v_____x_1216_, 0);
lean_dec(v_unused_1235_);
v___x_1220_ = v_____x_1216_;
v_isShared_1221_ = v_isSharedCheck_1234_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_snd_1218_);
lean_dec(v_____x_1216_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1234_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1233_; 
v_a_1222_ = lean_ctor_get(v_fst_1217_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_fst_1217_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1224_ = v_fst_1217_;
v_isShared_1225_ = v_isSharedCheck_1233_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v_fst_1217_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1233_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1229_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1227_);
v___x_1229_ = v___x_1220_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_snd_1218_);
v___x_1229_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_apply_2(v_toPure_1210_, lean_box(0), v___x_1229_);
return v___x_1230_;
}
}
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1258_; 
v_a_1236_ = lean_ctor_get(v_fst_1217_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_fst_1217_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1238_ = v_fst_1217_;
v_isShared_1239_ = v_isSharedCheck_1258_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v_fst_1217_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1258_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
uint8_t v___x_1240_; 
v___x_1240_ = lean_unbox(v_a_1236_);
lean_dec(v_a_1236_);
if (v___x_1240_ == 0)
{
lean_object* v_snd_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_del_object(v___x_1238_);
lean_dec(v___x_1215_);
lean_dec(v_toPure_1210_);
v_snd_1241_ = lean_ctor_get(v_____x_1216_, 1);
lean_inc(v_snd_1241_);
lean_dec_ref(v_____x_1216_);
v___x_1242_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v___x_1211_, v_inst_1212_, v_snd_1241_);
v___x_1243_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v___x_1242_, v___f_1214_);
return v___x_1243_;
}
else
{
lean_object* v_snd_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v___f_1214_);
lean_dec(v_toBind_1213_);
lean_dec_ref(v_inst_1212_);
v_snd_1244_ = lean_ctor_get(v_____x_1216_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_____x_1216_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v_____x_1216_, 0);
lean_dec(v_unused_1257_);
v___x_1246_ = v_____x_1216_;
v_isShared_1247_ = v_isSharedCheck_1256_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_snd_1244_);
lean_dec(v_____x_1216_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1256_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1215_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1248_);
v___x_1250_ = v___x_1238_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1252_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1250_);
v___x_1252_ = v___x_1246_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_snd_1244_);
v___x_1252_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_apply_2(v_toPure_1210_, lean_box(0), v___x_1252_);
return v___x_1253_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed(lean_object* v_toPure_1259_, lean_object* v___x_1260_, lean_object* v_inst_1261_, lean_object* v_toBind_1262_, lean_object* v___f_1263_, lean_object* v___x_1264_, lean_object* v_____x_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(v_toPure_1259_, v___x_1260_, v_inst_1261_, v_toBind_1262_, v___f_1263_, v___x_1264_, v_____x_1265_);
lean_dec(v___x_1260_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(lean_object* v_toPure_1267_, lean_object* v_inst_1268_, lean_object* v___y_1269_, lean_object* v_toBind_1270_, lean_object* v___f_1271_, lean_object* v_____x_1272_){
_start:
{
lean_object* v_fst_1273_; 
v_fst_1273_ = lean_ctor_get(v_____x_1272_, 0);
lean_inc(v_fst_1273_);
if (lean_obj_tag(v_fst_1273_) == 0)
{
lean_object* v_snd_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v___f_1271_);
lean_dec(v_toBind_1270_);
lean_dec_ref(v_inst_1268_);
v_snd_1274_ = lean_ctor_get(v_____x_1272_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_____x_1272_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v_____x_1272_, 0);
lean_dec(v_unused_1291_);
v___x_1276_ = v_____x_1272_;
v_isShared_1277_ = v_isSharedCheck_1290_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_snd_1274_);
lean_dec(v_____x_1272_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1290_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1289_; 
v_a_1278_ = lean_ctor_get(v_fst_1273_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_fst_1273_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1280_ = v_fst_1273_;
v_isShared_1281_ = v_isSharedCheck_1289_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v_fst_1273_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1289_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1285_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1283_);
v___x_1285_ = v___x_1276_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_snd_1274_);
v___x_1285_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_apply_2(v_toPure_1267_, lean_box(0), v___x_1285_);
return v___x_1286_;
}
}
}
}
}
else
{
lean_object* v_snd_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec_ref_known(v_fst_1273_, 1);
lean_dec(v_toPure_1267_);
v_snd_1292_ = lean_ctor_get(v_____x_1272_, 1);
lean_inc(v_snd_1292_);
lean_dec_ref(v_____x_1272_);
v___x_1293_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_1268_, v___y_1269_, v_snd_1292_);
v___x_1294_ = lean_apply_4(v_toBind_1270_, lean_box(0), lean_box(0), v___x_1293_, v___f_1271_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed(lean_object* v_toPure_1295_, lean_object* v_inst_1296_, lean_object* v___y_1297_, lean_object* v_toBind_1298_, lean_object* v___f_1299_, lean_object* v_____x_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(v_toPure_1295_, v_inst_1296_, v___y_1297_, v_toBind_1298_, v___f_1299_, v_____x_1300_);
lean_dec_ref(v___y_1297_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(lean_object* v_toPure_1302_, lean_object* v___x_1303_, lean_object* v___x_1304_, lean_object* v_inst_1305_, lean_object* v_toBind_1306_, lean_object* v___f_1307_, lean_object* v___y_1308_, lean_object* v_____x_1309_){
_start:
{
lean_object* v_fst_1310_; 
v_fst_1310_ = lean_ctor_get(v_____x_1309_, 0);
lean_inc(v_fst_1310_);
if (lean_obj_tag(v_fst_1310_) == 0)
{
lean_object* v_snd_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v___f_1307_);
lean_dec(v_toBind_1306_);
lean_dec_ref(v_inst_1305_);
lean_dec(v___x_1304_);
v_snd_1311_ = lean_ctor_get(v_____x_1309_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_____x_1309_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v_____x_1309_, 0);
lean_dec(v_unused_1328_);
v___x_1313_ = v_____x_1309_;
v_isShared_1314_ = v_isSharedCheck_1327_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_snd_1311_);
lean_dec(v_____x_1309_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1327_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1326_; 
v_a_1315_ = lean_ctor_get(v_fst_1310_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_fst_1310_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1317_ = v_fst_1310_;
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v_fst_1310_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1326_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1322_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1320_);
v___x_1322_ = v___x_1313_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_snd_1311_);
v___x_1322_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_apply_2(v_toPure_1302_, lean_box(0), v___x_1322_);
return v___x_1323_;
}
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v_snd_1330_; lean_object* v_added_1331_; lean_object* v___x_1332_; lean_object* v___f_1333_; lean_object* v___f_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_a_1329_ = lean_ctor_get(v_fst_1310_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v_fst_1310_, 1);
v_snd_1330_ = lean_ctor_get(v_____x_1309_, 1);
lean_inc(v_snd_1330_);
lean_dec_ref(v_____x_1309_);
v_added_1331_ = lean_ctor_get(v_a_1329_, 1);
lean_inc_ref(v_added_1331_);
lean_dec(v_a_1329_);
v___x_1332_ = lean_array_get(v___x_1303_, v_added_1331_, v___x_1304_);
lean_dec_ref(v_added_1331_);
lean_inc_n(v_toBind_1306_, 2);
lean_inc_ref_n(v_inst_1305_, 2);
lean_inc(v___x_1332_);
lean_inc(v_toPure_1302_);
v___f_1333_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1333_, 0, v_toPure_1302_);
lean_closure_set(v___f_1333_, 1, v___x_1332_);
lean_closure_set(v___f_1333_, 2, v_inst_1305_);
lean_closure_set(v___f_1333_, 3, v_toBind_1306_);
lean_closure_set(v___f_1333_, 4, v___f_1307_);
lean_closure_set(v___f_1333_, 5, v___x_1304_);
lean_inc_ref(v___y_1308_);
v___f_1334_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_1334_, 0, v_toPure_1302_);
lean_closure_set(v___f_1334_, 1, v_inst_1305_);
lean_closure_set(v___f_1334_, 2, v___y_1308_);
lean_closure_set(v___f_1334_, 3, v_toBind_1306_);
lean_closure_set(v___f_1334_, 4, v___f_1333_);
v___x_1335_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v___x_1332_, v_inst_1305_, v_snd_1330_);
lean_dec(v___x_1332_);
v___x_1336_ = lean_apply_4(v_toBind_1306_, lean_box(0), lean_box(0), v___x_1335_, v___f_1334_);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed(lean_object* v_toPure_1337_, lean_object* v___x_1338_, lean_object* v___x_1339_, lean_object* v_inst_1340_, lean_object* v_toBind_1341_, lean_object* v___f_1342_, lean_object* v___y_1343_, lean_object* v_____x_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(v_toPure_1337_, v___x_1338_, v___x_1339_, v_inst_1340_, v_toBind_1341_, v___f_1342_, v___y_1343_, v_____x_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___x_1338_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7(lean_object* v_toPure_1346_, lean_object* v_toBind_1347_, lean_object* v___f_1348_, lean_object* v___x_1349_, lean_object* v___x_1350_, lean_object* v_inst_1351_, lean_object* v_b_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = lean_nat_dec_lt(v___x_1355_, v_b_1352_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec_ref(v_inst_1351_);
lean_dec(v___x_1350_);
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v_b_1352_);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v___y_1354_);
v___x_1360_ = lean_apply_2(v_toPure_1346_, lean_box(0), v___x_1359_);
v___x_1361_ = lean_apply_4(v_toBind_1347_, lean_box(0), lean_box(0), v___x_1360_, v___f_1348_);
return v___x_1361_;
}
else
{
lean_object* v___x_1362_; lean_object* v___f_1363_; lean_object* v___f_1364_; lean_object* v___f_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1362_ = lean_nat_sub(v_b_1352_, v___x_1349_);
lean_dec(v_b_1352_);
lean_inc(v___x_1362_);
lean_inc_n(v_toPure_1346_, 3);
v___f_1363_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1363_, 0, v_toPure_1346_);
lean_closure_set(v___f_1363_, 1, v___x_1362_);
lean_inc_ref(v___y_1353_);
lean_inc_n(v_toBind_1347_, 3);
v___f_1364_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1364_, 0, v_toPure_1346_);
lean_closure_set(v___f_1364_, 1, v___x_1350_);
lean_closure_set(v___f_1364_, 2, v___x_1362_);
lean_closure_set(v___f_1364_, 3, v_inst_1351_);
lean_closure_set(v___f_1364_, 4, v_toBind_1347_);
lean_closure_set(v___f_1364_, 5, v___f_1363_);
lean_closure_set(v___f_1364_, 6, v___y_1353_);
v___f_1365_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1365_, 0, v_toPure_1346_);
lean_inc_ref(v___y_1354_);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___y_1354_);
lean_ctor_set(v___x_1366_, 1, v___y_1354_);
v___x_1367_ = lean_apply_2(v_toPure_1346_, lean_box(0), v___x_1366_);
v___x_1368_ = lean_apply_4(v_toBind_1347_, lean_box(0), lean_box(0), v___x_1367_, v___f_1365_);
v___x_1369_ = lean_apply_4(v_toBind_1347_, lean_box(0), lean_box(0), v___x_1368_, v___f_1364_);
v___x_1370_ = lean_apply_4(v_toBind_1347_, lean_box(0), lean_box(0), v___x_1369_, v___f_1348_);
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed(lean_object* v_toPure_1371_, lean_object* v_toBind_1372_, lean_object* v___f_1373_, lean_object* v___x_1374_, lean_object* v___x_1375_, lean_object* v_inst_1376_, lean_object* v_b_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7(v_toPure_1371_, v_toBind_1372_, v___f_1373_, v___x_1374_, v___x_1375_, v_inst_1376_, v_b_1377_, v___y_1378_, v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___x_1374_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(lean_object* v_toPure_1381_, lean_object* v_toBind_1382_, lean_object* v___f_1383_, lean_object* v___x_1384_, lean_object* v_inst_1385_, lean_object* v___x_1386_, lean_object* v_a_1387_, lean_object* v___f_1388_, lean_object* v_____x_1389_){
_start:
{
lean_object* v_fst_1390_; 
v_fst_1390_ = lean_ctor_get(v_____x_1389_, 0);
lean_inc(v_fst_1390_);
if (lean_obj_tag(v_fst_1390_) == 0)
{
lean_object* v_snd_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v___f_1388_);
lean_dec_ref(v___x_1386_);
lean_dec_ref(v_inst_1385_);
lean_dec(v___x_1384_);
lean_dec(v___f_1383_);
lean_dec(v_toBind_1382_);
v_snd_1391_ = lean_ctor_get(v_____x_1389_, 1);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_____x_1389_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v_____x_1389_, 0);
lean_dec(v_unused_1408_);
v___x_1393_ = v_____x_1389_;
v_isShared_1394_ = v_isSharedCheck_1407_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_snd_1391_);
lean_dec(v_____x_1389_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1407_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1406_; 
v_a_1395_ = lean_ctor_get(v_fst_1390_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_fst_1390_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1397_ = v_fst_1390_;
v_isShared_1398_ = v_isSharedCheck_1406_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v_fst_1390_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1406_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1402_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1400_);
v___x_1402_ = v___x_1393_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_snd_1391_);
v___x_1402_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_apply_2(v_toPure_1381_, lean_box(0), v___x_1402_);
return v___x_1403_;
}
}
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v_snd_1410_; lean_object* v_added_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___f_1414_; lean_object* v___x_1415_; lean_object* v___x_5968__overap_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v_a_1409_ = lean_ctor_get(v_fst_1390_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v_fst_1390_, 1);
v_snd_1410_ = lean_ctor_get(v_____x_1389_, 1);
lean_inc(v_snd_1410_);
lean_dec_ref(v_____x_1389_);
v_added_1411_ = lean_ctor_get(v_a_1409_, 1);
lean_inc_ref(v_added_1411_);
lean_dec(v_a_1409_);
v___x_1412_ = lean_array_get_size(v_added_1411_);
lean_dec_ref(v_added_1411_);
v___x_1413_ = lean_unsigned_to_nat(1u);
lean_inc(v_toBind_1382_);
v___f_1414_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed), 9, 6);
lean_closure_set(v___f_1414_, 0, v_toPure_1381_);
lean_closure_set(v___f_1414_, 1, v_toBind_1382_);
lean_closure_set(v___f_1414_, 2, v___f_1383_);
lean_closure_set(v___f_1414_, 3, v___x_1413_);
lean_closure_set(v___f_1414_, 4, v___x_1384_);
lean_closure_set(v___f_1414_, 5, v_inst_1385_);
v___x_1415_ = lean_nat_sub(v___x_1412_, v___x_1413_);
v___x_5968__overap_1416_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_1386_, v___f_1414_, v___x_1415_);
lean_inc_ref(v_a_1387_);
v___x_1417_ = lean_apply_2(v___x_5968__overap_1416_, v_a_1387_, v_snd_1410_);
v___x_1418_ = lean_apply_4(v_toBind_1382_, lean_box(0), lean_box(0), v___x_1417_, v___f_1388_);
return v___x_1418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed(lean_object* v_toPure_1419_, lean_object* v_toBind_1420_, lean_object* v___f_1421_, lean_object* v___x_1422_, lean_object* v_inst_1423_, lean_object* v___x_1424_, lean_object* v_a_1425_, lean_object* v___f_1426_, lean_object* v_____x_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(v_toPure_1419_, v_toBind_1420_, v___f_1421_, v___x_1422_, v_inst_1423_, v___x_1424_, v_a_1425_, v___f_1426_, v_____x_1427_);
lean_dec_ref(v_a_1425_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(lean_object* v_inst_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___f_1432_; lean_object* v___f_1433_; lean_object* v___f_1434_; lean_object* v___f_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___f_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v_toApplicative_1453_; lean_object* v_toBind_1454_; lean_object* v_toPure_1455_; lean_object* v___f_1456_; lean_object* v___f_1457_; lean_object* v___x_1458_; lean_object* v___f_1459_; lean_object* v___f_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_inc_ref_n(v_inst_1429_, 7);
v___f_1432_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1432_, 0, v_inst_1429_);
v___f_1433_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1433_, 0, v_inst_1429_);
v___f_1434_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1434_, 0, v_inst_1429_);
v___f_1435_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1435_, 0, v_inst_1429_);
v___x_1436_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1436_, 0, lean_box(0));
lean_closure_set(v___x_1436_, 1, lean_box(0));
lean_closure_set(v___x_1436_, 2, v_inst_1429_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
lean_ctor_set(v___x_1437_, 1, v___f_1432_);
v___x_1438_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1438_, 0, lean_box(0));
lean_closure_set(v___x_1438_, 1, lean_box(0));
lean_closure_set(v___x_1438_, 2, v_inst_1429_);
v___x_1439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
lean_ctor_set(v___x_1439_, 2, v___f_1433_);
lean_ctor_set(v___x_1439_, 3, v___f_1434_);
lean_ctor_set(v___x_1439_, 4, v___f_1435_);
v___x_1440_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1440_, 0, lean_box(0));
lean_closure_set(v___x_1440_, 1, lean_box(0));
lean_closure_set(v___x_1440_, 2, v_inst_1429_);
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
lean_inc_ref_n(v___x_1441_, 6);
v___f_1442_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1442_, 0, v___x_1441_);
v___f_1443_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1443_, 0, v___x_1441_);
v___f_1444_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1444_, 0, v___x_1441_);
v___f_1445_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1445_, 0, v___x_1441_);
v___x_1446_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1446_, 0, lean_box(0));
lean_closure_set(v___x_1446_, 1, lean_box(0));
lean_closure_set(v___x_1446_, 2, v___x_1441_);
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
lean_ctor_set(v___x_1447_, 1, v___f_1442_);
v___x_1448_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1448_, 0, lean_box(0));
lean_closure_set(v___x_1448_, 1, lean_box(0));
lean_closure_set(v___x_1448_, 2, v___x_1441_);
v___x_1449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
lean_ctor_set(v___x_1449_, 2, v___f_1443_);
lean_ctor_set(v___x_1449_, 3, v___f_1444_);
lean_ctor_set(v___x_1449_, 4, v___f_1445_);
v___x_1450_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1450_, 0, lean_box(0));
lean_closure_set(v___x_1450_, 1, lean_box(0));
lean_closure_set(v___x_1450_, 2, v___x_1441_);
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = l_ReaderT_instMonad___redArg(v___x_1451_);
v_toApplicative_1453_ = lean_ctor_get(v_inst_1429_, 0);
v_toBind_1454_ = lean_ctor_get(v_inst_1429_, 1);
lean_inc_n(v_toBind_1454_, 3);
v_toPure_1455_ = lean_ctor_get(v_toApplicative_1453_, 1);
lean_inc_n(v_toPure_1455_, 5);
v___f_1456_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1456_, 0, v_toPure_1455_);
v___f_1457_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1457_, 0, v_toPure_1455_);
v___x_1458_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1430_);
v___f_1459_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed), 9, 8);
lean_closure_set(v___f_1459_, 0, v_toPure_1455_);
lean_closure_set(v___f_1459_, 1, v_toBind_1454_);
lean_closure_set(v___f_1459_, 2, v___f_1457_);
lean_closure_set(v___f_1459_, 3, v___x_1458_);
lean_closure_set(v___f_1459_, 4, v_inst_1429_);
lean_closure_set(v___f_1459_, 5, v___x_1452_);
lean_closure_set(v___f_1459_, 6, v_a_1430_);
lean_closure_set(v___f_1459_, 7, v___f_1456_);
v___f_1460_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1460_, 0, v_toPure_1455_);
lean_inc_ref(v_a_1431_);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v_a_1431_);
lean_ctor_set(v___x_1461_, 1, v_a_1431_);
v___x_1462_ = lean_apply_2(v_toPure_1455_, lean_box(0), v___x_1461_);
v___x_1463_ = lean_apply_4(v_toBind_1454_, lean_box(0), lean_box(0), v___x_1462_, v___f_1460_);
v___x_1464_ = lean_apply_4(v_toBind_1454_, lean_box(0), lean_box(0), v___x_1463_, v___f_1459_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___boxed(lean_object* v_inst_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1465_, v_a_1466_, v_a_1467_);
lean_dec_ref(v_a_1466_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(lean_object* v_m_1469_, lean_object* v_inst_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1470_, v_a_1471_, v_a_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___boxed(lean_object* v_m_1474_, lean_object* v_inst_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(v_m_1474_, v_inst_1475_, v_a_1476_, v_a_1477_);
lean_dec_ref(v_a_1476_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(lean_object* v_toApplicative_1479_, lean_object* v_inst_1480_, lean_object* v_a_1481_, lean_object* v_____x_1482_){
_start:
{
lean_object* v_fst_1483_; 
v_fst_1483_ = lean_ctor_get(v_____x_1482_, 0);
lean_inc(v_fst_1483_);
if (lean_obj_tag(v_fst_1483_) == 0)
{
lean_object* v_snd_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v_inst_1480_);
v_snd_1484_ = lean_ctor_get(v_____x_1482_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_____x_1482_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v_____x_1482_, 0);
lean_dec(v_unused_1502_);
v___x_1486_ = v_____x_1482_;
v_isShared_1487_ = v_isSharedCheck_1501_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_snd_1484_);
lean_dec(v_____x_1482_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1501_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1500_; 
v_a_1488_ = lean_ctor_get(v_fst_1483_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_fst_1483_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1490_ = v_fst_1483_;
v_isShared_1491_ = v_isSharedCheck_1500_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v_fst_1483_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1500_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_toPure_1492_; lean_object* v___x_1494_; 
v_toPure_1492_ = lean_ctor_get(v_toApplicative_1479_, 1);
lean_inc(v_toPure_1492_);
lean_dec_ref(v_toApplicative_1479_);
if (v_isShared_1491_ == 0)
{
v___x_1494_ = v___x_1490_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1488_);
v___x_1494_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1494_);
v___x_1496_ = v___x_1486_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_snd_1484_);
v___x_1496_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_apply_2(v_toPure_1492_, lean_box(0), v___x_1496_);
return v___x_1497_;
}
}
}
}
}
else
{
lean_object* v_a_1503_; uint8_t v_found_1504_; 
v_a_1503_ = lean_ctor_get(v_fst_1483_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v_fst_1483_, 1);
v_found_1504_ = lean_ctor_get_uint8(v_a_1503_, sizeof(void*)*3);
lean_dec(v_a_1503_);
if (v_found_1504_ == 0)
{
lean_object* v_snd_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1515_; 
lean_dec_ref(v_inst_1480_);
v_snd_1505_ = lean_ctor_get(v_____x_1482_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_____x_1482_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v_____x_1482_, 0);
lean_dec(v_unused_1516_);
v___x_1507_ = v_____x_1482_;
v_isShared_1508_ = v_isSharedCheck_1515_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_snd_1505_);
lean_dec(v_____x_1482_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1515_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v_toPure_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v_toPure_1509_ = lean_ctor_get(v_toApplicative_1479_, 1);
lean_inc(v_toPure_1509_);
lean_dec_ref(v_toApplicative_1479_);
v___x_1510_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0));
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1510_);
v___x_1512_ = v___x_1507_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_snd_1505_);
v___x_1512_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_apply_2(v_toPure_1509_, lean_box(0), v___x_1512_);
return v___x_1513_;
}
}
}
else
{
lean_object* v_snd_1517_; lean_object* v___x_1518_; 
lean_dec_ref(v_toApplicative_1479_);
v_snd_1517_ = lean_ctor_get(v_____x_1482_, 1);
lean_inc(v_snd_1517_);
lean_dec_ref(v_____x_1482_);
v___x_1518_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1480_, v_a_1481_, v_snd_1517_);
return v___x_1518_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed(lean_object* v_toApplicative_1519_, lean_object* v_inst_1520_, lean_object* v_a_1521_, lean_object* v_____x_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(v_toApplicative_1519_, v_inst_1520_, v_a_1521_, v_____x_1522_);
lean_dec_ref(v_a_1521_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2(lean_object* v_toApplicative_1524_, lean_object* v_toBind_1525_, lean_object* v___f_1526_, lean_object* v_____x_1527_){
_start:
{
lean_object* v_fst_1528_; 
v_fst_1528_ = lean_ctor_get(v_____x_1527_, 0);
if (lean_obj_tag(v_fst_1528_) == 0)
{
lean_object* v_toPure_1529_; lean_object* v___x_1530_; 
lean_dec(v___f_1526_);
lean_dec(v_toBind_1525_);
v_toPure_1529_ = lean_ctor_get(v_toApplicative_1524_, 1);
lean_inc(v_toPure_1529_);
lean_dec_ref(v_toApplicative_1524_);
v___x_1530_ = lean_apply_2(v_toPure_1529_, lean_box(0), v_____x_1527_);
return v___x_1530_;
}
else
{
lean_object* v_snd_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1543_; 
v_snd_1531_ = lean_ctor_get(v_____x_1527_, 1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_____x_1527_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v_____x_1527_, 0);
lean_dec(v_unused_1544_);
v___x_1533_ = v_____x_1527_;
v_isShared_1534_ = v_isSharedCheck_1543_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_snd_1531_);
lean_dec(v_____x_1527_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1543_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v_toPure_1535_; lean_object* v___f_1536_; lean_object* v___x_1538_; 
v_toPure_1535_ = lean_ctor_get(v_toApplicative_1524_, 1);
lean_inc_n(v_toPure_1535_, 2);
lean_dec_ref(v_toApplicative_1524_);
v___f_1536_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1536_, 0, v_toPure_1535_);
lean_inc(v_snd_1531_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v_snd_1531_);
v___x_1538_ = v___x_1533_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_snd_1531_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_snd_1531_);
v___x_1538_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = lean_apply_2(v_toPure_1535_, lean_box(0), v___x_1538_);
lean_inc(v_toBind_1525_);
v___x_1540_ = lean_apply_4(v_toBind_1525_, lean_box(0), lean_box(0), v___x_1539_, v___f_1536_);
v___x_1541_ = lean_apply_4(v_toBind_1525_, lean_box(0), lean_box(0), v___x_1540_, v___f_1526_);
return v___x_1541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(lean_object* v_inst_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v_toApplicative_1548_; lean_object* v_toBind_1549_; lean_object* v___f_1550_; lean_object* v___f_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_toApplicative_1548_ = lean_ctor_get(v_inst_1545_, 0);
v_toBind_1549_ = lean_ctor_get(v_inst_1545_, 1);
lean_inc_n(v_toBind_1549_, 2);
lean_inc_ref(v_a_1546_);
lean_inc_ref(v_inst_1545_);
lean_inc_ref_n(v_toApplicative_1548_, 2);
v___f_1550_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1550_, 0, v_toApplicative_1548_);
lean_closure_set(v___f_1550_, 1, v_inst_1545_);
lean_closure_set(v___f_1550_, 2, v_a_1546_);
v___f_1551_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1551_, 0, v_toApplicative_1548_);
lean_closure_set(v___f_1551_, 1, v_toBind_1549_);
lean_closure_set(v___f_1551_, 2, v___f_1550_);
v___x_1552_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1545_, v_a_1546_, v_a_1547_);
v___x_1553_ = lean_apply_4(v_toBind_1549_, lean_box(0), lean_box(0), v___x_1552_, v___f_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___boxed(lean_object* v_inst_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1554_, v_a_1555_, v_a_1556_);
lean_dec_ref(v_a_1555_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(lean_object* v_m_1558_, lean_object* v_inst_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1559_, v_a_1560_, v_a_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___boxed(lean_object* v_m_1563_, lean_object* v_inst_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(v_m_1563_, v_inst_1564_, v_a_1565_, v_a_1566_);
lean_dec_ref(v_a_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0(lean_object* v_toPure_1568_, lean_object* v_____x_1569_){
_start:
{
lean_object* v_snd_1570_; lean_object* v_fst_1571_; lean_object* v_cur_1572_; lean_object* v_numCalls_1573_; uint8_t v_found_1574_; uint8_t v___y_1576_; 
v_snd_1570_ = lean_ctor_get(v_____x_1569_, 1);
v_fst_1571_ = lean_ctor_get(v_____x_1569_, 0);
v_cur_1572_ = lean_ctor_get(v_snd_1570_, 0);
v_numCalls_1573_ = lean_ctor_get(v_snd_1570_, 2);
v_found_1574_ = lean_ctor_get_uint8(v_snd_1570_, sizeof(void*)*3);
if (v_found_1574_ == 0)
{
uint8_t v___x_1579_; 
v___x_1579_ = 0;
v___y_1576_ = v___x_1579_;
goto v___jp_1575_;
}
else
{
if (lean_obj_tag(v_fst_1571_) == 0)
{
uint8_t v___x_1580_; 
v___x_1580_ = 1;
v___y_1576_ = v___x_1580_;
goto v___jp_1575_;
}
else
{
uint8_t v___x_1581_; 
v___x_1581_ = 2;
v___y_1576_ = v___x_1581_;
goto v___jp_1575_;
}
}
v___jp_1575_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_inc(v_numCalls_1573_);
lean_inc_ref(v_cur_1572_);
v___x_1577_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1577_, 0, v_cur_1572_);
lean_ctor_set(v___x_1577_, 1, v_numCalls_1573_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*2, v___y_1576_);
v___x_1578_ = lean_apply_2(v_toPure_1568_, lean_box(0), v___x_1577_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed(lean_object* v_toPure_1582_, lean_object* v_____x_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__0(v_toPure_1582_, v_____x_1583_);
lean_dec_ref(v_____x_1583_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1(lean_object* v_initialMask_1587_, lean_object* v_test_1588_, lean_object* v_maxCalls_1589_, lean_object* v_inst_1590_, lean_object* v_toBind_1591_, lean_object* v___f_1592_, lean_object* v_toPure_1593_, uint8_t v_____do__lift_1594_){
_start:
{
if (v_____do__lift_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec(v_toPure_1593_);
lean_inc_ref(v_initialMask_1587_);
v___x_1595_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1595_, 0, v_initialMask_1587_);
lean_ctor_set(v___x_1595_, 1, v_test_1588_);
lean_ctor_set(v___x_1595_, 2, v_maxCalls_1589_);
v___x_1596_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0));
v___x_1597_ = lean_unsigned_to_nat(1u);
v___x_1598_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1598_, 0, v_initialMask_1587_);
lean_ctor_set(v___x_1598_, 1, v___x_1596_);
lean_ctor_set(v___x_1598_, 2, v___x_1597_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*3, v_____do__lift_1594_);
v___x_1599_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1590_, v___x_1595_, v___x_1598_);
lean_dec_ref_known(v___x_1595_, 3);
v___x_1600_ = lean_apply_4(v_toBind_1591_, lean_box(0), lean_box(0), v___x_1599_, v___f_1592_);
return v___x_1600_;
}
else
{
uint8_t v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v___f_1592_);
lean_dec(v_toBind_1591_);
lean_dec_ref(v_inst_1590_);
lean_dec(v_maxCalls_1589_);
lean_dec(v_test_1588_);
v___x_1601_ = 2;
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1603_, 0, v_initialMask_1587_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*2, v___x_1601_);
v___x_1604_ = lean_apply_2(v_toPure_1593_, lean_box(0), v___x_1603_);
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed(lean_object* v_initialMask_1605_, lean_object* v_test_1606_, lean_object* v_maxCalls_1607_, lean_object* v_inst_1608_, lean_object* v_toBind_1609_, lean_object* v___f_1610_, lean_object* v_toPure_1611_, lean_object* v_____do__lift_1612_){
_start:
{
uint8_t v_____do__lift_162__boxed_1613_; lean_object* v_res_1614_; 
v_____do__lift_162__boxed_1613_ = lean_unbox(v_____do__lift_1612_);
v_res_1614_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__1(v_initialMask_1605_, v_test_1606_, v_maxCalls_1607_, v_inst_1608_, v_toBind_1609_, v___f_1610_, v_toPure_1611_, v_____do__lift_162__boxed_1613_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg(lean_object* v_inst_1615_, lean_object* v_initialMask_1616_, lean_object* v_test_1617_, lean_object* v_maxCalls_1618_){
_start:
{
lean_object* v_toApplicative_1619_; lean_object* v_toBind_1620_; lean_object* v_toPure_1621_; lean_object* v___x_1622_; lean_object* v___f_1623_; lean_object* v___f_1624_; lean_object* v___x_1625_; 
v_toApplicative_1619_ = lean_ctor_get(v_inst_1615_, 0);
v_toBind_1620_ = lean_ctor_get(v_inst_1615_, 1);
lean_inc_n(v_toBind_1620_, 2);
v_toPure_1621_ = lean_ctor_get(v_toApplicative_1619_, 1);
lean_inc_n(v_toPure_1621_, 2);
lean_inc(v_test_1617_);
lean_inc_ref(v_initialMask_1616_);
v___x_1622_ = lean_apply_1(v_test_1617_, v_initialMask_1616_);
v___f_1623_ = lean_alloc_closure((void*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1623_, 0, v_toPure_1621_);
v___f_1624_ = lean_alloc_closure((void*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1624_, 0, v_initialMask_1616_);
lean_closure_set(v___f_1624_, 1, v_test_1617_);
lean_closure_set(v___f_1624_, 2, v_maxCalls_1618_);
lean_closure_set(v___f_1624_, 3, v_inst_1615_);
lean_closure_set(v___f_1624_, 4, v_toBind_1620_);
lean_closure_set(v___f_1624_, 5, v___f_1623_);
lean_closure_set(v___f_1624_, 6, v_toPure_1621_);
v___x_1625_ = lean_apply_4(v_toBind_1620_, lean_box(0), lean_box(0), v___x_1622_, v___f_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search(lean_object* v_m_1626_, lean_object* v_inst_1627_, lean_object* v_initialMask_1628_, lean_object* v_test_1629_, lean_object* v_maxCalls_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Util_ParamMinimizer_search___redArg(v_inst_1627_, v_initialMask_1628_, v_test_1629_, v_maxCalls_1630_);
return v___x_1631_;
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
