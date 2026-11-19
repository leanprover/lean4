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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Util_ParamMinimizer_Status_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Util_ParamMinimizer_Status_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg(lean_object* v_missing_22_){
_start:
{
lean_inc(v_missing_22_);
return v_missing_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg___boxed(lean_object* v_missing_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg(v_missing_23_);
lean_dec(v_missing_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_missing_28_){
_start:
{
lean_inc(v_missing_28_);
return v_missing_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_missing_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Util_ParamMinimizer_Status_missing_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_missing_32_);
lean_dec(v_missing_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg(lean_object* v_approx_35_){
_start:
{
lean_inc(v_approx_35_);
return v_approx_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg___boxed(lean_object* v_approx_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg(v_approx_36_);
lean_dec(v_approx_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_approx_41_){
_start:
{
lean_inc(v_approx_41_);
return v_approx_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_approx_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Util_ParamMinimizer_Status_approx_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_approx_45_);
lean_dec(v_approx_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg(lean_object* v_precise_48_){
_start:
{
lean_inc(v_precise_48_);
return v_precise_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg___boxed(lean_object* v_precise_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg(v_precise_49_);
lean_dec(v_precise_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_precise_54_){
_start:
{
lean_inc(v_precise_54_);
return v_precise_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_precise_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Util_ParamMinimizer_Status_precise_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_precise_58_);
lean_dec(v_precise_58_);
return v_res_60_;
}
}
static uint8_t _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus_default(void){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
static uint8_t _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(2u);
v___x_73_ = lean_nat_to_int(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_to_int(v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr(uint8_t v_x_76_, lean_object* v_prec_77_){
_start:
{
lean_object* v___y_79_; lean_object* v___y_86_; lean_object* v___y_93_; 
switch(v_x_76_)
{
case 0:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(1024u);
v___x_100_ = lean_nat_dec_le(v___x_99_, v_prec_77_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6);
v___y_79_ = v___x_101_;
goto v___jp_78_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7);
v___y_79_ = v___x_102_;
goto v___jp_78_;
}
}
case 1:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(1024u);
v___x_104_ = lean_nat_dec_le(v___x_103_, v_prec_77_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6);
v___y_86_ = v___x_105_;
goto v___jp_85_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7);
v___y_86_ = v___x_106_;
goto v___jp_85_;
}
}
default: 
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(1024u);
v___x_108_ = lean_nat_dec_le(v___x_107_, v_prec_77_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6);
v___y_93_ = v___x_109_;
goto v___jp_92_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7);
v___y_93_ = v___x_110_;
goto v___jp_92_;
}
}
}
v___jp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_80_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1));
lean_inc(v___y_79_);
v___x_81_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_81_, 0, v___y_79_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = 0;
v___x_83_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1, v___x_82_);
v___x_84_ = l_Repr_addAppParen(v___x_83_, v_prec_77_);
return v___x_84_;
}
v___jp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_87_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3));
lean_inc(v___y_86_);
v___x_88_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_88_, 0, v___y_86_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = 0;
v___x_90_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*1, v___x_89_);
v___x_91_ = l_Repr_addAppParen(v___x_90_, v_prec_77_);
return v___x_91_;
}
v___jp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_94_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5));
lean_inc(v___y_93_);
v___x_95_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_95_, 0, v___y_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = 0;
v___x_97_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*1, v___x_96_);
v___x_98_ = l_Repr_addAppParen(v___x_97_, v_prec_77_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr___boxed(lean_object* v_x_111_, lean_object* v_prec_112_){
_start:
{
uint8_t v_x_171__boxed_113_; lean_object* v_res_114_; 
v_x_171__boxed_113_ = lean_unbox(v_x_111_);
v_res_114_ = l_Lean_Util_ParamMinimizer_instReprStatus_repr(v_x_171__boxed_113_, v_prec_112_);
lean_dec(v_prec_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0(lean_object* v_toPure_117_, lean_object* v_____x_118_){
_start:
{
lean_object* v_fst_119_; lean_object* v_snd_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_129_; 
v_fst_119_ = lean_ctor_get(v_____x_118_, 0);
v_snd_120_ = lean_ctor_get(v_____x_118_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_____x_118_);
if (v_isSharedCheck_129_ == 0)
{
v___x_122_ = v_____x_118_;
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_snd_120_);
lean_inc(v_fst_119_);
lean_dec(v_____x_118_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v_fst_119_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_124_);
v___x_126_ = v___x_122_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_snd_120_);
v___x_126_ = v_reuseFailAlloc_128_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; 
v___x_127_ = lean_apply_2(v_toPure_117_, lean_box(0), v___x_126_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(lean_object* v_inst_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_toApplicative_132_; lean_object* v_toBind_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_156_; 
v_toApplicative_132_ = lean_ctor_get(v_inst_130_, 0);
v_toBind_133_ = lean_ctor_get(v_inst_130_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_inst_130_);
if (v_isSharedCheck_156_ == 0)
{
v___x_135_ = v_inst_130_;
v_isShared_136_ = v_isSharedCheck_156_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_toBind_133_);
lean_inc(v_toApplicative_132_);
lean_dec(v_inst_130_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_156_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v_toPure_137_; lean_object* v_cur_138_; lean_object* v_added_139_; lean_object* v_numCalls_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_155_; 
v_toPure_137_ = lean_ctor_get(v_toApplicative_132_, 1);
lean_inc(v_toPure_137_);
lean_dec_ref(v_toApplicative_132_);
v_cur_138_ = lean_ctor_get(v_a_131_, 0);
v_added_139_ = lean_ctor_get(v_a_131_, 1);
v_numCalls_140_ = lean_ctor_get(v_a_131_, 2);
v_isSharedCheck_155_ = !lean_is_exclusive(v_a_131_);
if (v_isSharedCheck_155_ == 0)
{
v___x_142_ = v_a_131_;
v_isShared_143_ = v_isSharedCheck_155_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_numCalls_140_);
lean_inc(v_added_139_);
lean_inc(v_cur_138_);
lean_dec(v_a_131_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_155_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___f_144_; lean_object* v___x_145_; uint8_t v___x_146_; lean_object* v___x_148_; 
lean_inc(v_toPure_137_);
v___f_144_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_144_, 0, v_toPure_137_);
v___x_145_ = lean_box(0);
v___x_146_ = 1;
if (v_isShared_143_ == 0)
{
v___x_148_ = v___x_142_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_cur_138_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_added_139_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_numCalls_140_);
v___x_148_ = v_reuseFailAlloc_154_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_150_; 
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*3, v___x_146_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v___x_148_);
lean_ctor_set(v___x_135_, 0, v___x_145_);
v___x_150_ = v___x_135_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_145_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_148_);
v___x_150_ = v_reuseFailAlloc_153_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_apply_2(v_toPure_137_, lean_box(0), v___x_150_);
v___x_152_ = lean_apply_4(v_toBind_133_, lean_box(0), lean_box(0), v___x_151_, v___f_144_);
return v___x_152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound(lean_object* v_m_157_, lean_object* v_inst_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(v_inst_158_, v_a_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___boxed(lean_object* v_m_162_, lean_object* v_inst_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound(v_m_162_, v_inst_163_, v_a_164_, v_a_165_);
lean_dec_ref(v_a_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___redArg(lean_object* v_inst_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_toApplicative_169_; lean_object* v_toBind_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_195_; 
v_toApplicative_169_ = lean_ctor_get(v_inst_167_, 0);
v_toBind_170_ = lean_ctor_get(v_inst_167_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_inst_167_);
if (v_isSharedCheck_195_ == 0)
{
v___x_172_ = v_inst_167_;
v_isShared_173_ = v_isSharedCheck_195_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_toBind_170_);
lean_inc(v_toApplicative_169_);
lean_dec(v_inst_167_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_195_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v_toPure_174_; lean_object* v_cur_175_; lean_object* v_added_176_; lean_object* v_numCalls_177_; uint8_t v_found_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_194_; 
v_toPure_174_ = lean_ctor_get(v_toApplicative_169_, 1);
lean_inc(v_toPure_174_);
lean_dec_ref(v_toApplicative_169_);
v_cur_175_ = lean_ctor_get(v_a_168_, 0);
v_added_176_ = lean_ctor_get(v_a_168_, 1);
v_numCalls_177_ = lean_ctor_get(v_a_168_, 2);
v_found_178_ = lean_ctor_get_uint8(v_a_168_, sizeof(void*)*3);
v_isSharedCheck_194_ = !lean_is_exclusive(v_a_168_);
if (v_isSharedCheck_194_ == 0)
{
v___x_180_ = v_a_168_;
v_isShared_181_ = v_isSharedCheck_194_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_numCalls_177_);
lean_inc(v_added_176_);
lean_inc(v_cur_175_);
lean_dec(v_a_168_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_194_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___f_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
lean_inc(v_toPure_174_);
v___f_182_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_182_, 0, v_toPure_174_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = lean_nat_add(v_numCalls_177_, v___x_184_);
lean_dec(v_numCalls_177_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 2, v___x_185_);
v___x_187_ = v___x_180_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_cur_175_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_added_176_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v___x_185_);
lean_ctor_set_uint8(v_reuseFailAlloc_193_, sizeof(void*)*3, v_found_178_);
v___x_187_ = v_reuseFailAlloc_193_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_189_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 1, v___x_187_);
lean_ctor_set(v___x_172_, 0, v___x_183_);
v___x_189_ = v___x_172_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_187_);
v___x_189_ = v_reuseFailAlloc_192_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_apply_2(v_toPure_174_, lean_box(0), v___x_189_);
v___x_191_ = lean_apply_4(v_toBind_170_, lean_box(0), lean_box(0), v___x_190_, v___f_182_);
return v___x_191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls(lean_object* v_m_196_, lean_object* v_inst_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___redArg(v_inst_197_, v_a_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___boxed(lean_object* v_m_201_, lean_object* v_inst_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls(v_m_201_, v_inst_202_, v_a_203_, v_a_204_);
lean_dec_ref(v_a_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(lean_object* v_i_206_, lean_object* v_inst_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_toApplicative_209_; lean_object* v_toBind_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_237_; 
v_toApplicative_209_ = lean_ctor_get(v_inst_207_, 0);
v_toBind_210_ = lean_ctor_get(v_inst_207_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v_inst_207_);
if (v_isSharedCheck_237_ == 0)
{
v___x_212_ = v_inst_207_;
v_isShared_213_ = v_isSharedCheck_237_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_toBind_210_);
lean_inc(v_toApplicative_209_);
lean_dec(v_inst_207_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_237_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_toPure_214_; lean_object* v_cur_215_; lean_object* v_added_216_; lean_object* v_numCalls_217_; uint8_t v_found_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_236_; 
v_toPure_214_ = lean_ctor_get(v_toApplicative_209_, 1);
lean_inc(v_toPure_214_);
lean_dec_ref(v_toApplicative_209_);
v_cur_215_ = lean_ctor_get(v_a_208_, 0);
v_added_216_ = lean_ctor_get(v_a_208_, 1);
v_numCalls_217_ = lean_ctor_get(v_a_208_, 2);
v_found_218_ = lean_ctor_get_uint8(v_a_208_, sizeof(void*)*3);
v_isSharedCheck_236_ = !lean_is_exclusive(v_a_208_);
if (v_isSharedCheck_236_ == 0)
{
v___x_220_ = v_a_208_;
v_isShared_221_ = v_isSharedCheck_236_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_numCalls_217_);
lean_inc(v_added_216_);
lean_inc(v_cur_215_);
lean_dec(v_a_208_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_236_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___f_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
lean_inc(v_toPure_214_);
v___f_222_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_222_, 0, v_toPure_214_);
v___x_223_ = lean_box(0);
v___x_224_ = 1;
v___x_225_ = lean_box(v___x_224_);
v___x_226_ = lean_array_set(v_cur_215_, v_i_206_, v___x_225_);
v___x_227_ = lean_array_push(v_added_216_, v_i_206_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_227_);
lean_ctor_set(v___x_220_, 0, v___x_226_);
v___x_229_ = v___x_220_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_numCalls_217_);
lean_ctor_set_uint8(v_reuseFailAlloc_235_, sizeof(void*)*3, v_found_218_);
v___x_229_ = v_reuseFailAlloc_235_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_231_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v___x_229_);
lean_ctor_set(v___x_212_, 0, v___x_223_);
v___x_231_ = v___x_212_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_229_);
v___x_231_ = v_reuseFailAlloc_234_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_apply_2(v_toPure_214_, lean_box(0), v___x_231_);
v___x_233_ = lean_apply_4(v_toBind_210_, lean_box(0), lean_box(0), v___x_232_, v___f_222_);
return v___x_233_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add(lean_object* v_m_238_, lean_object* v_i_239_, lean_object* v_inst_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(v_i_239_, v_inst_240_, v_a_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___boxed(lean_object* v_m_244_, lean_object* v_i_245_, lean_object* v_inst_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add(v_m_244_, v_i_245_, v_inst_246_, v_a_247_, v_a_248_);
lean_dec_ref(v_a_247_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(lean_object* v_i_250_, lean_object* v_inst_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_toApplicative_253_; lean_object* v_toBind_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_280_; 
v_toApplicative_253_ = lean_ctor_get(v_inst_251_, 0);
v_toBind_254_ = lean_ctor_get(v_inst_251_, 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v_inst_251_);
if (v_isSharedCheck_280_ == 0)
{
v___x_256_ = v_inst_251_;
v_isShared_257_ = v_isSharedCheck_280_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_toBind_254_);
lean_inc(v_toApplicative_253_);
lean_dec(v_inst_251_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_280_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v_toPure_258_; lean_object* v_cur_259_; lean_object* v_added_260_; lean_object* v_numCalls_261_; uint8_t v_found_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_279_; 
v_toPure_258_ = lean_ctor_get(v_toApplicative_253_, 1);
lean_inc(v_toPure_258_);
lean_dec_ref(v_toApplicative_253_);
v_cur_259_ = lean_ctor_get(v_a_252_, 0);
v_added_260_ = lean_ctor_get(v_a_252_, 1);
v_numCalls_261_ = lean_ctor_get(v_a_252_, 2);
v_found_262_ = lean_ctor_get_uint8(v_a_252_, sizeof(void*)*3);
v_isSharedCheck_279_ = !lean_is_exclusive(v_a_252_);
if (v_isSharedCheck_279_ == 0)
{
v___x_264_ = v_a_252_;
v_isShared_265_ = v_isSharedCheck_279_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_numCalls_261_);
lean_inc(v_added_260_);
lean_inc(v_cur_259_);
lean_dec(v_a_252_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_279_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___f_266_; lean_object* v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
lean_inc(v_toPure_258_);
v___f_266_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_266_, 0, v_toPure_258_);
v___x_267_ = lean_box(0);
v___x_268_ = 0;
v___x_269_ = lean_box(v___x_268_);
v___x_270_ = lean_array_set(v_cur_259_, v_i_250_, v___x_269_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_270_);
v___x_272_ = v___x_264_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_added_260_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_numCalls_261_);
lean_ctor_set_uint8(v_reuseFailAlloc_278_, sizeof(void*)*3, v_found_262_);
v___x_272_ = v_reuseFailAlloc_278_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_274_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_272_);
lean_ctor_set(v___x_256_, 0, v___x_267_);
v___x_274_ = v___x_256_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_272_);
v___x_274_ = v_reuseFailAlloc_277_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_apply_2(v_toPure_258_, lean_box(0), v___x_274_);
v___x_276_ = lean_apply_4(v_toBind_254_, lean_box(0), lean_box(0), v___x_275_, v___f_266_);
return v___x_276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg___boxed(lean_object* v_i_281_, lean_object* v_inst_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v_i_281_, v_inst_282_, v_a_283_);
lean_dec(v_i_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase(lean_object* v_m_285_, lean_object* v_i_286_, lean_object* v_inst_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v_i_286_, v_inst_287_, v_a_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___boxed(lean_object* v_m_291_, lean_object* v_i_292_, lean_object* v_inst_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase(v_m_291_, v_i_292_, v_inst_293_, v_a_294_, v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_i_292_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(lean_object* v_i_297_, lean_object* v_inst_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_toApplicative_300_; lean_object* v_toBind_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_327_; 
v_toApplicative_300_ = lean_ctor_get(v_inst_298_, 0);
v_toBind_301_ = lean_ctor_get(v_inst_298_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_inst_298_);
if (v_isSharedCheck_327_ == 0)
{
v___x_303_ = v_inst_298_;
v_isShared_304_ = v_isSharedCheck_327_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_toBind_301_);
lean_inc(v_toApplicative_300_);
lean_dec(v_inst_298_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_327_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_toPure_305_; lean_object* v_cur_306_; lean_object* v_added_307_; lean_object* v_numCalls_308_; uint8_t v_found_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_326_; 
v_toPure_305_ = lean_ctor_get(v_toApplicative_300_, 1);
lean_inc(v_toPure_305_);
lean_dec_ref(v_toApplicative_300_);
v_cur_306_ = lean_ctor_get(v_a_299_, 0);
v_added_307_ = lean_ctor_get(v_a_299_, 1);
v_numCalls_308_ = lean_ctor_get(v_a_299_, 2);
v_found_309_ = lean_ctor_get_uint8(v_a_299_, sizeof(void*)*3);
v_isSharedCheck_326_ = !lean_is_exclusive(v_a_299_);
if (v_isSharedCheck_326_ == 0)
{
v___x_311_ = v_a_299_;
v_isShared_312_ = v_isSharedCheck_326_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_numCalls_308_);
lean_inc(v_added_307_);
lean_inc(v_cur_306_);
lean_dec(v_a_299_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_326_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___f_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
lean_inc(v_toPure_305_);
v___f_313_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_313_, 0, v_toPure_305_);
v___x_314_ = lean_box(0);
v___x_315_ = 1;
v___x_316_ = lean_box(v___x_315_);
v___x_317_ = lean_array_set(v_cur_306_, v_i_297_, v___x_316_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_317_);
v___x_319_ = v___x_311_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_added_307_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_numCalls_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_325_, sizeof(void*)*3, v_found_309_);
v___x_319_ = v_reuseFailAlloc_325_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_321_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v___x_319_);
lean_ctor_set(v___x_303_, 0, v___x_314_);
v___x_321_ = v___x_303_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___x_319_);
v___x_321_ = v_reuseFailAlloc_324_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_apply_2(v_toPure_305_, lean_box(0), v___x_321_);
v___x_323_ = lean_apply_4(v_toBind_301_, lean_box(0), lean_box(0), v___x_322_, v___f_313_);
return v___x_323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg___boxed(lean_object* v_i_328_, lean_object* v_inst_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v_i_328_, v_inst_329_, v_a_330_);
lean_dec(v_i_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore(lean_object* v_m_332_, lean_object* v_i_333_, lean_object* v_inst_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v_i_333_, v_inst_334_, v_a_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___boxed(lean_object* v_m_338_, lean_object* v_i_339_, lean_object* v_inst_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore(v_m_338_, v_i_339_, v_inst_340_, v_a_341_, v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_i_339_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(lean_object* v_toPure_344_, uint8_t v___x_345_, lean_object* v_____x_346_){
_start:
{
lean_object* v_fst_347_; 
v_fst_347_ = lean_ctor_get(v_____x_346_, 0);
lean_inc(v_fst_347_);
if (lean_obj_tag(v_fst_347_) == 0)
{
lean_object* v_snd_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_364_; 
v_snd_348_ = lean_ctor_get(v_____x_346_, 1);
v_isSharedCheck_364_ = !lean_is_exclusive(v_____x_346_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v_____x_346_, 0);
lean_dec(v_unused_365_);
v___x_350_ = v_____x_346_;
v_isShared_351_ = v_isSharedCheck_364_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_snd_348_);
lean_dec(v_____x_346_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_364_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_363_; 
v_a_352_ = lean_ctor_get(v_fst_347_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_fst_347_);
if (v_isSharedCheck_363_ == 0)
{
v___x_354_ = v_fst_347_;
v_isShared_355_ = v_isSharedCheck_363_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v_fst_347_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_363_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_362_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_359_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_357_);
v___x_359_ = v___x_350_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_snd_348_);
v___x_359_ = v_reuseFailAlloc_361_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; 
v___x_360_ = lean_apply_2(v_toPure_344_, lean_box(0), v___x_359_);
return v___x_360_;
}
}
}
}
}
else
{
lean_object* v_snd_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_383_; 
v_snd_366_ = lean_ctor_get(v_____x_346_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_____x_346_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_____x_346_, 0);
lean_dec(v_unused_384_);
v___x_368_ = v_____x_346_;
v_isShared_369_ = v_isSharedCheck_383_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_snd_366_);
lean_dec(v_____x_346_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_383_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_381_; 
v_isSharedCheck_381_ = !lean_is_exclusive(v_fst_347_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v_fst_347_, 0);
lean_dec(v_unused_382_);
v___x_371_ = v_fst_347_;
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
else
{
lean_dec(v_fst_347_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_box(v___x_345_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_380_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_377_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_375_);
v___x_377_ = v___x_368_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_snd_366_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; 
v___x_378_ = lean_apply_2(v_toPure_344_, lean_box(0), v___x_377_);
return v___x_378_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed(lean_object* v_toPure_385_, lean_object* v___x_386_, lean_object* v_____x_387_){
_start:
{
uint8_t v___x_6887__boxed_388_; lean_object* v_res_389_; 
v___x_6887__boxed_388_ = lean_unbox(v___x_386_);
v_res_389_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(v_toPure_385_, v___x_6887__boxed_388_, v_____x_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1(lean_object* v_toPure_390_, lean_object* v_inst_391_, lean_object* v_toBind_392_, lean_object* v___f_393_, lean_object* v_____x_394_){
_start:
{
lean_object* v_fst_395_; 
v_fst_395_ = lean_ctor_get(v_____x_394_, 0);
if (lean_obj_tag(v_fst_395_) == 0)
{
lean_object* v___x_396_; 
lean_dec(v___f_393_);
lean_dec(v_toBind_392_);
lean_dec_ref(v_inst_391_);
v___x_396_ = lean_apply_2(v_toPure_390_, lean_box(0), v_____x_394_);
return v___x_396_;
}
else
{
lean_object* v_a_397_; uint8_t v___x_398_; 
v_a_397_ = lean_ctor_get(v_fst_395_, 0);
v___x_398_ = lean_unbox(v_a_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec(v___f_393_);
lean_dec(v_toBind_392_);
lean_dec_ref(v_inst_391_);
v___x_399_ = lean_apply_2(v_toPure_390_, lean_box(0), v_____x_394_);
return v___x_399_;
}
else
{
lean_object* v_snd_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec(v_toPure_390_);
v_snd_400_ = lean_ctor_get(v_____x_394_, 1);
lean_inc(v_snd_400_);
lean_dec_ref(v_____x_394_);
v___x_401_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(v_inst_391_, v_snd_400_);
v___x_402_ = lean_apply_4(v_toBind_392_, lean_box(0), lean_box(0), v___x_401_, v___f_393_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__2(lean_object* v_toPure_403_, lean_object* v_____x_404_){
_start:
{
lean_object* v_fst_405_; lean_object* v_snd_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_415_; 
v_fst_405_ = lean_ctor_get(v_____x_404_, 0);
v_snd_406_ = lean_ctor_get(v_____x_404_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v_____x_404_);
if (v_isSharedCheck_415_ == 0)
{
v___x_408_ = v_____x_404_;
v_isShared_409_ = v_isSharedCheck_415_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_snd_406_);
lean_inc(v_fst_405_);
lean_dec(v_____x_404_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_415_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_410_, 0, v_fst_405_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_410_);
v___x_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_snd_406_);
v___x_412_ = v_reuseFailAlloc_414_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; 
v___x_413_ = lean_apply_2(v_toPure_403_, lean_box(0), v___x_412_);
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(lean_object* v_snd_416_, lean_object* v_toPure_417_, uint8_t v_a_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_box(v_a_418_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v_snd_416_);
v___x_421_ = lean_apply_2(v_toPure_417_, lean_box(0), v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3___boxed(lean_object* v_snd_422_, lean_object* v_toPure_423_, lean_object* v_a_424_){
_start:
{
uint8_t v_a_boxed_425_; lean_object* v_res_426_; 
v_a_boxed_425_ = lean_unbox(v_a_424_);
v_res_426_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(v_snd_422_, v_toPure_423_, v_a_boxed_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4(lean_object* v_toPure_427_, lean_object* v_a_428_, lean_object* v_toBind_429_, lean_object* v___f_430_, lean_object* v_____x_431_){
_start:
{
lean_object* v_fst_432_; 
v_fst_432_ = lean_ctor_get(v_____x_431_, 0);
lean_inc(v_fst_432_);
if (lean_obj_tag(v_fst_432_) == 0)
{
lean_object* v_snd_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_449_; 
lean_dec(v___f_430_);
lean_dec(v_toBind_429_);
lean_dec_ref(v_a_428_);
v_snd_433_ = lean_ctor_get(v_____x_431_, 1);
v_isSharedCheck_449_ = !lean_is_exclusive(v_____x_431_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v_____x_431_, 0);
lean_dec(v_unused_450_);
v___x_435_ = v_____x_431_;
v_isShared_436_ = v_isSharedCheck_449_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_snd_433_);
lean_dec(v_____x_431_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_449_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_448_; 
v_a_437_ = lean_ctor_get(v_fst_432_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v_fst_432_);
if (v_isSharedCheck_448_ == 0)
{
v___x_439_ = v_fst_432_;
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v_fst_432_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_447_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_444_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_442_);
v___x_444_ = v___x_435_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_snd_433_);
v___x_444_ = v_reuseFailAlloc_446_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; 
v___x_445_ = lean_apply_2(v_toPure_427_, lean_box(0), v___x_444_);
return v___x_445_;
}
}
}
}
}
else
{
lean_object* v_a_451_; lean_object* v_snd_452_; lean_object* v_test_453_; lean_object* v_cur_454_; lean_object* v___x_455_; lean_object* v___f_456_; lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_a_451_ = lean_ctor_get(v_fst_432_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v_fst_432_, 1);
v_snd_452_ = lean_ctor_get(v_____x_431_, 1);
lean_inc(v_snd_452_);
lean_dec_ref(v_____x_431_);
v_test_453_ = lean_ctor_get(v_a_428_, 1);
lean_inc(v_test_453_);
lean_dec_ref(v_a_428_);
v_cur_454_ = lean_ctor_get(v_a_451_, 0);
lean_inc_ref(v_cur_454_);
lean_dec(v_a_451_);
v___x_455_ = lean_apply_1(v_test_453_, v_cur_454_);
lean_inc(v_toPure_427_);
v___f_456_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__2), 2, 1);
lean_closure_set(v___f_456_, 0, v_toPure_427_);
v___f_457_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_457_, 0, v_snd_452_);
lean_closure_set(v___f_457_, 1, v_toPure_427_);
lean_inc_n(v_toBind_429_, 2);
v___x_458_ = lean_apply_4(v_toBind_429_, lean_box(0), lean_box(0), v___x_455_, v___f_457_);
v___x_459_ = lean_apply_4(v_toBind_429_, lean_box(0), lean_box(0), v___x_458_, v___f_456_);
v___x_460_ = lean_apply_4(v_toBind_429_, lean_box(0), lean_box(0), v___x_459_, v___f_430_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5(lean_object* v_toPure_461_, lean_object* v_____x_462_){
_start:
{
lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_473_; 
v_fst_463_ = lean_ctor_get(v_____x_462_, 0);
v_snd_464_ = lean_ctor_get(v_____x_462_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v_____x_462_);
if (v_isSharedCheck_473_ == 0)
{
v___x_466_ = v_____x_462_;
v_isShared_467_ = v_isSharedCheck_473_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_snd_464_);
lean_inc(v_fst_463_);
lean_dec(v_____x_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_473_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v_fst_463_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_468_);
v___x_470_ = v___x_466_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_snd_464_);
v___x_470_ = v_reuseFailAlloc_472_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_471_; 
v___x_471_ = lean_apply_2(v_toPure_461_, lean_box(0), v___x_470_);
return v___x_471_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6(lean_object* v_toPure_474_, lean_object* v_toBind_475_, lean_object* v___f_476_, lean_object* v_____x_477_){
_start:
{
lean_object* v_fst_478_; 
v_fst_478_ = lean_ctor_get(v_____x_477_, 0);
lean_inc(v_fst_478_);
if (lean_obj_tag(v_fst_478_) == 0)
{
lean_object* v_snd_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_495_; 
lean_dec(v___f_476_);
lean_dec(v_toBind_475_);
v_snd_479_ = lean_ctor_get(v_____x_477_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v_____x_477_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; 
v_unused_496_ = lean_ctor_get(v_____x_477_, 0);
lean_dec(v_unused_496_);
v___x_481_ = v_____x_477_;
v_isShared_482_ = v_isSharedCheck_495_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_snd_479_);
lean_dec(v_____x_477_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_495_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_494_; 
v_a_483_ = lean_ctor_get(v_fst_478_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v_fst_478_);
if (v_isSharedCheck_494_ == 0)
{
v___x_485_ = v_fst_478_;
v_isShared_486_ = v_isSharedCheck_494_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v_fst_478_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_494_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_493_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_488_);
v___x_490_ = v___x_481_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_snd_479_);
v___x_490_ = v_reuseFailAlloc_492_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; 
v___x_491_ = lean_apply_2(v_toPure_474_, lean_box(0), v___x_490_);
return v___x_491_;
}
}
}
}
}
else
{
lean_object* v_snd_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_510_; 
v_snd_497_ = lean_ctor_get(v_____x_477_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v_____x_477_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v_____x_477_, 0);
lean_dec(v_unused_511_);
v___x_499_ = v_____x_477_;
v_isShared_500_ = v_isSharedCheck_510_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_snd_497_);
lean_dec(v_____x_477_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_510_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_a_501_; lean_object* v___f_502_; lean_object* v___f_503_; lean_object* v___x_505_; 
v_a_501_ = lean_ctor_get(v_fst_478_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v_fst_478_, 1);
lean_inc(v_toBind_475_);
lean_inc_n(v_toPure_474_, 2);
v___f_502_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4), 5, 4);
lean_closure_set(v___f_502_, 0, v_toPure_474_);
lean_closure_set(v___f_502_, 1, v_a_501_);
lean_closure_set(v___f_502_, 2, v_toBind_475_);
lean_closure_set(v___f_502_, 3, v___f_476_);
v___f_503_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_503_, 0, v_toPure_474_);
lean_inc(v_snd_497_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v_snd_497_);
v___x_505_ = v___x_499_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_snd_497_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_snd_497_);
v___x_505_ = v_reuseFailAlloc_509_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_apply_2(v_toPure_474_, lean_box(0), v___x_505_);
lean_inc(v_toBind_475_);
v___x_507_ = lean_apply_4(v_toBind_475_, lean_box(0), lean_box(0), v___x_506_, v___f_503_);
v___x_508_ = lean_apply_4(v_toBind_475_, lean_box(0), lean_box(0), v___x_507_, v___f_502_);
return v___x_508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7(lean_object* v_toPure_512_, lean_object* v_a_513_, lean_object* v_toBind_514_, lean_object* v___f_515_, lean_object* v_____x_516_){
_start:
{
lean_object* v_fst_517_; 
v_fst_517_ = lean_ctor_get(v_____x_516_, 0);
lean_inc(v_fst_517_);
if (lean_obj_tag(v_fst_517_) == 0)
{
lean_object* v_snd_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_534_; 
lean_dec(v___f_515_);
lean_dec(v_toBind_514_);
v_snd_518_ = lean_ctor_get(v_____x_516_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_____x_516_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; 
v_unused_535_ = lean_ctor_get(v_____x_516_, 0);
lean_dec(v_unused_535_);
v___x_520_ = v_____x_516_;
v_isShared_521_ = v_isSharedCheck_534_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_snd_518_);
lean_dec(v_____x_516_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_534_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_533_; 
v_a_522_ = lean_ctor_get(v_fst_517_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_fst_517_);
if (v_isSharedCheck_533_ == 0)
{
v___x_524_ = v_fst_517_;
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v_fst_517_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_533_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_532_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_529_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_527_);
v___x_529_ = v___x_520_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_snd_518_);
v___x_529_ = v_reuseFailAlloc_531_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = lean_apply_2(v_toPure_512_, lean_box(0), v___x_529_);
return v___x_530_;
}
}
}
}
}
else
{
lean_object* v_snd_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_553_; 
v_snd_536_ = lean_ctor_get(v_____x_516_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_____x_516_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v_____x_516_, 0);
lean_dec(v_unused_554_);
v___x_538_ = v_____x_516_;
v_isShared_539_ = v_isSharedCheck_553_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_snd_536_);
lean_dec(v_____x_516_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_553_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_551_; 
v_isSharedCheck_551_ = !lean_is_exclusive(v_fst_517_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v_fst_517_, 0);
lean_dec(v_unused_552_);
v___x_541_ = v_fst_517_;
v_isShared_542_ = v_isSharedCheck_551_;
goto v_resetjp_540_;
}
else
{
lean_dec(v_fst_517_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_551_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
lean_inc_ref(v_a_513_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v_a_513_);
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_513_);
v___x_544_ = v_reuseFailAlloc_550_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_546_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_544_);
v___x_546_ = v___x_538_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_snd_536_);
v___x_546_ = v_reuseFailAlloc_549_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_apply_2(v_toPure_512_, lean_box(0), v___x_546_);
v___x_548_ = lean_apply_4(v_toBind_514_, lean_box(0), lean_box(0), v___x_547_, v___f_515_);
return v___x_548_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7___boxed(lean_object* v_toPure_555_, lean_object* v_a_556_, lean_object* v_toBind_557_, lean_object* v___f_558_, lean_object* v_____x_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7(v_toPure_555_, v_a_556_, v_toBind_557_, v___f_558_, v_____x_559_);
lean_dec_ref(v_a_556_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(lean_object* v_toPure_563_, lean_object* v_inst_564_, lean_object* v_toBind_565_, lean_object* v_a_566_, lean_object* v_maxCalls_567_, lean_object* v_____x_568_){
_start:
{
lean_object* v_fst_569_; lean_object* v_snd_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_620_; 
v_fst_569_ = lean_ctor_get(v_____x_568_, 0);
v_snd_570_ = lean_ctor_get(v_____x_568_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v_____x_568_);
if (v_isSharedCheck_620_ == 0)
{
v___x_572_ = v_____x_568_;
v_isShared_573_ = v_isSharedCheck_620_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_snd_570_);
lean_inc(v_fst_569_);
lean_dec(v_____x_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_620_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
if (lean_obj_tag(v_fst_569_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_611_; 
lean_del_object(v___x_572_);
lean_dec(v_toBind_565_);
lean_dec_ref(v_inst_564_);
v_a_602_ = lean_ctor_get(v_fst_569_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_fst_569_);
if (v_isSharedCheck_611_ == 0)
{
v___x_604_ = v_fst_569_;
v_isShared_605_ = v_isSharedCheck_611_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v_fst_569_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_611_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_610_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_snd_570_);
v___x_609_ = lean_apply_2(v_toPure_563_, lean_box(0), v___x_608_);
return v___x_609_;
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_a_612_ = lean_ctor_get(v_fst_569_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v_fst_569_, 1);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_nat_dec_lt(v___x_613_, v_maxCalls_567_);
if (v___x_614_ == 0)
{
lean_dec(v_a_612_);
goto v___jp_574_;
}
else
{
lean_object* v_numCalls_615_; uint8_t v___x_616_; 
v_numCalls_615_ = lean_ctor_get(v_a_612_, 2);
lean_inc(v_numCalls_615_);
lean_dec(v_a_612_);
v___x_616_ = lean_nat_dec_le(v_maxCalls_567_, v_numCalls_615_);
lean_dec(v_numCalls_615_);
if (v___x_616_ == 0)
{
goto v___jp_574_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_del_object(v___x_572_);
lean_dec(v_toBind_565_);
lean_dec_ref(v_inst_564_);
v___x_617_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0));
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v_snd_570_);
v___x_619_ = lean_apply_2(v_toPure_563_, lean_box(0), v___x_618_);
return v___x_619_;
}
}
}
v___jp_574_:
{
lean_object* v_cur_575_; lean_object* v_added_576_; lean_object* v_numCalls_577_; uint8_t v_found_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_601_; 
v_cur_575_ = lean_ctor_get(v_snd_570_, 0);
v_added_576_ = lean_ctor_get(v_snd_570_, 1);
v_numCalls_577_ = lean_ctor_get(v_snd_570_, 2);
v_found_578_ = lean_ctor_get_uint8(v_snd_570_, sizeof(void*)*3);
v_isSharedCheck_601_ = !lean_is_exclusive(v_snd_570_);
if (v_isSharedCheck_601_ == 0)
{
v___x_580_ = v_snd_570_;
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_numCalls_577_);
lean_inc(v_added_576_);
lean_inc(v_cur_575_);
lean_dec(v_snd_570_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___f_584_; lean_object* v___f_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_582_ = 1;
v___x_583_ = lean_box(v___x_582_);
lean_inc_n(v_toPure_563_, 5);
v___f_584_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_584_, 0, v_toPure_563_);
lean_closure_set(v___f_584_, 1, v___x_583_);
lean_inc_n(v_toBind_565_, 3);
v___f_585_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1), 5, 4);
lean_closure_set(v___f_585_, 0, v_toPure_563_);
lean_closure_set(v___f_585_, 1, v_inst_564_);
lean_closure_set(v___f_585_, 2, v_toBind_565_);
lean_closure_set(v___f_585_, 3, v___f_584_);
v___f_586_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6), 4, 3);
lean_closure_set(v___f_586_, 0, v_toPure_563_);
lean_closure_set(v___f_586_, 1, v_toBind_565_);
lean_closure_set(v___f_586_, 2, v___f_585_);
lean_inc_ref(v_a_566_);
v___f_587_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7___boxed), 5, 4);
lean_closure_set(v___f_587_, 0, v_toPure_563_);
lean_closure_set(v___f_587_, 1, v_a_566_);
lean_closure_set(v___f_587_, 2, v_toBind_565_);
lean_closure_set(v___f_587_, 3, v___f_586_);
v___f_588_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_588_, 0, v_toPure_563_);
v___x_589_ = lean_box(0);
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_nat_add(v_numCalls_577_, v___x_590_);
lean_dec(v_numCalls_577_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 2, v___x_591_);
v___x_593_ = v___x_580_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_cur_575_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_added_576_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v___x_591_);
lean_ctor_set_uint8(v_reuseFailAlloc_600_, sizeof(void*)*3, v_found_578_);
v___x_593_ = v_reuseFailAlloc_600_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_595_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v___x_593_);
lean_ctor_set(v___x_572_, 0, v___x_589_);
v___x_595_ = v___x_572_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_593_);
v___x_595_ = v_reuseFailAlloc_599_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_apply_2(v_toPure_563_, lean_box(0), v___x_595_);
lean_inc(v_toBind_565_);
v___x_597_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v___x_596_, v___f_588_);
v___x_598_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v___x_597_, v___f_587_);
return v___x_598_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed(lean_object* v_toPure_621_, lean_object* v_inst_622_, lean_object* v_toBind_623_, lean_object* v_a_624_, lean_object* v_maxCalls_625_, lean_object* v_____x_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(v_toPure_621_, v_inst_622_, v_toBind_623_, v_a_624_, v_maxCalls_625_, v_____x_626_);
lean_dec(v_maxCalls_625_);
lean_dec_ref(v_a_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(lean_object* v_toPure_628_, lean_object* v_inst_629_, lean_object* v_toBind_630_, lean_object* v_a_631_, lean_object* v_____x_632_){
_start:
{
lean_object* v_fst_633_; 
v_fst_633_ = lean_ctor_get(v_____x_632_, 0);
lean_inc(v_fst_633_);
if (lean_obj_tag(v_fst_633_) == 0)
{
lean_object* v_snd_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_toBind_630_);
lean_dec_ref(v_inst_629_);
v_snd_634_ = lean_ctor_get(v_____x_632_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_____x_632_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v_____x_632_, 0);
lean_dec(v_unused_651_);
v___x_636_ = v_____x_632_;
v_isShared_637_ = v_isSharedCheck_650_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_snd_634_);
lean_dec(v_____x_632_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_650_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_649_; 
v_a_638_ = lean_ctor_get(v_fst_633_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v_fst_633_);
if (v_isSharedCheck_649_ == 0)
{
v___x_640_ = v_fst_633_;
v_isShared_641_ = v_isSharedCheck_649_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v_fst_633_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_649_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_648_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_645_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_643_);
v___x_645_ = v___x_636_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_snd_634_);
v___x_645_ = v_reuseFailAlloc_647_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; 
v___x_646_ = lean_apply_2(v_toPure_628_, lean_box(0), v___x_645_);
return v___x_646_;
}
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v_snd_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_666_; 
v_a_652_ = lean_ctor_get(v_fst_633_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v_fst_633_, 1);
v_snd_653_ = lean_ctor_get(v_____x_632_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_____x_632_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v_____x_632_, 0);
lean_dec(v_unused_667_);
v___x_655_ = v_____x_632_;
v_isShared_656_ = v_isSharedCheck_666_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_snd_653_);
lean_dec(v_____x_632_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_666_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_maxCalls_657_; lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___x_661_; 
v_maxCalls_657_ = lean_ctor_get(v_a_652_, 2);
lean_inc(v_maxCalls_657_);
lean_dec(v_a_652_);
lean_inc_ref(v_a_631_);
lean_inc(v_toBind_630_);
lean_inc_n(v_toPure_628_, 2);
v___f_658_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_658_, 0, v_toPure_628_);
lean_closure_set(v___f_658_, 1, v_inst_629_);
lean_closure_set(v___f_658_, 2, v_toBind_630_);
lean_closure_set(v___f_658_, 3, v_a_631_);
lean_closure_set(v___f_658_, 4, v_maxCalls_657_);
v___f_659_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_659_, 0, v_toPure_628_);
lean_inc(v_snd_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v_snd_653_);
v___x_661_ = v___x_655_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_snd_653_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_snd_653_);
v___x_661_ = v_reuseFailAlloc_665_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = lean_apply_2(v_toPure_628_, lean_box(0), v___x_661_);
lean_inc(v_toBind_630_);
v___x_663_ = lean_apply_4(v_toBind_630_, lean_box(0), lean_box(0), v___x_662_, v___f_659_);
v___x_664_ = lean_apply_4(v_toBind_630_, lean_box(0), lean_box(0), v___x_663_, v___f_658_);
return v___x_664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed(lean_object* v_toPure_668_, lean_object* v_inst_669_, lean_object* v_toBind_670_, lean_object* v_a_671_, lean_object* v_____x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(v_toPure_668_, v_inst_669_, v_toBind_670_, v_a_671_, v_____x_672_);
lean_dec_ref(v_a_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(lean_object* v_inst_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_toApplicative_677_; lean_object* v_toBind_678_; lean_object* v_toPure_679_; lean_object* v___f_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_toApplicative_677_ = lean_ctor_get(v_inst_674_, 0);
v_toBind_678_ = lean_ctor_get(v_inst_674_, 1);
lean_inc_n(v_toBind_678_, 2);
v_toPure_679_ = lean_ctor_get(v_toApplicative_677_, 1);
lean_inc_n(v_toPure_679_, 2);
lean_inc_ref_n(v_a_675_, 2);
v___f_680_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_680_, 0, v_toPure_679_);
lean_closure_set(v___f_680_, 1, v_inst_674_);
lean_closure_set(v___f_680_, 2, v_toBind_678_);
lean_closure_set(v___f_680_, 3, v_a_675_);
v___x_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_681_, 0, v_a_675_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v_a_676_);
v___x_683_ = lean_apply_2(v_toPure_679_, lean_box(0), v___x_682_);
v___x_684_ = lean_apply_4(v_toBind_678_, lean_box(0), lean_box(0), v___x_683_, v___f_680_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___boxed(lean_object* v_inst_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_685_, v_a_686_, v_a_687_);
lean_dec_ref(v_a_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(lean_object* v_m_689_, lean_object* v_inst_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_690_, v_a_691_, v_a_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___boxed(lean_object* v_m_694_, lean_object* v_inst_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(v_m_694_, v_inst_695_, v_a_696_, v_a_697_);
lean_dec_ref(v_a_696_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0(lean_object* v_toPure_699_, lean_object* v_____x_700_){
_start:
{
lean_object* v_fst_701_; 
v_fst_701_ = lean_ctor_get(v_____x_700_, 0);
lean_inc(v_fst_701_);
if (lean_obj_tag(v_fst_701_) == 0)
{
lean_object* v_snd_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_718_; 
v_snd_702_ = lean_ctor_get(v_____x_700_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_____x_700_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v_____x_700_, 0);
lean_dec(v_unused_719_);
v___x_704_ = v_____x_700_;
v_isShared_705_ = v_isSharedCheck_718_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_snd_702_);
lean_dec(v_____x_700_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_718_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_717_; 
v_a_706_ = lean_ctor_get(v_fst_701_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v_fst_701_);
if (v_isSharedCheck_717_ == 0)
{
v___x_708_ = v_fst_701_;
v_isShared_709_ = v_isSharedCheck_717_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v_fst_701_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_717_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_716_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_711_);
v___x_713_ = v___x_704_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_snd_702_);
v___x_713_ = v_reuseFailAlloc_715_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; 
v___x_714_ = lean_apply_2(v_toPure_699_, lean_box(0), v___x_713_);
return v___x_714_;
}
}
}
}
}
else
{
lean_object* v_snd_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_736_; 
v_snd_720_ = lean_ctor_get(v_____x_700_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v_____x_700_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v_____x_700_, 0);
lean_dec(v_unused_737_);
v___x_722_ = v_____x_700_;
v_isShared_723_ = v_isSharedCheck_736_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_snd_720_);
lean_dec(v_____x_700_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_736_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_735_; 
v_a_724_ = lean_ctor_get(v_fst_701_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v_fst_701_);
if (v_isSharedCheck_735_ == 0)
{
v___x_726_ = v_fst_701_;
v_isShared_727_ = v_isSharedCheck_735_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v_fst_701_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_735_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_734_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_731_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_729_);
v___x_731_ = v___x_722_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_snd_720_);
v___x_731_ = v_reuseFailAlloc_733_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_732_; 
v___x_732_ = lean_apply_2(v_toPure_699_, lean_box(0), v___x_731_);
return v___x_732_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1(lean_object* v_toPure_738_, lean_object* v___x_739_, lean_object* v_____x_740_){
_start:
{
lean_object* v_fst_741_; 
v_fst_741_ = lean_ctor_get(v_____x_740_, 0);
lean_inc(v_fst_741_);
if (lean_obj_tag(v_fst_741_) == 0)
{
lean_object* v_snd_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_758_; 
v_snd_742_ = lean_ctor_get(v_____x_740_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_____x_740_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v_____x_740_, 0);
lean_dec(v_unused_759_);
v___x_744_ = v_____x_740_;
v_isShared_745_ = v_isSharedCheck_758_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_snd_742_);
lean_dec(v_____x_740_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_758_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_757_; 
v_a_746_ = lean_ctor_get(v_fst_741_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v_fst_741_);
if (v_isSharedCheck_757_ == 0)
{
v___x_748_ = v_fst_741_;
v_isShared_749_ = v_isSharedCheck_757_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v_fst_741_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_757_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_756_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_753_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_751_);
v___x_753_ = v___x_744_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_snd_742_);
v___x_753_ = v_reuseFailAlloc_755_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; 
v___x_754_ = lean_apply_2(v_toPure_738_, lean_box(0), v___x_753_);
return v___x_754_;
}
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_787_; 
v_a_760_ = lean_ctor_get(v_fst_741_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v_fst_741_);
if (v_isSharedCheck_787_ == 0)
{
v___x_762_ = v_fst_741_;
v_isShared_763_ = v_isSharedCheck_787_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v_fst_741_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_787_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_fst_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_785_; 
v_fst_764_ = lean_ctor_get(v_a_760_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v_a_760_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_a_760_, 1);
lean_dec(v_unused_786_);
v___x_766_ = v_a_760_;
v_isShared_767_ = v_isSharedCheck_785_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_fst_764_);
lean_dec(v_a_760_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_785_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
if (lean_obj_tag(v_fst_764_) == 0)
{
lean_object* v_snd_768_; lean_object* v___x_770_; 
v_snd_768_ = lean_ctor_get(v_____x_740_, 1);
lean_inc(v_snd_768_);
lean_dec_ref(v_____x_740_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_739_);
v___x_770_ = v___x_762_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_739_);
v___x_770_ = v_reuseFailAlloc_775_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_772_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v_snd_768_);
lean_ctor_set(v___x_766_, 0, v___x_770_);
v___x_772_ = v___x_766_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_snd_768_);
v___x_772_ = v_reuseFailAlloc_774_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; 
v___x_773_ = lean_apply_2(v_toPure_738_, lean_box(0), v___x_772_);
return v___x_773_;
}
}
}
else
{
lean_object* v_snd_776_; lean_object* v_val_777_; lean_object* v___x_779_; 
v_snd_776_ = lean_ctor_get(v_____x_740_, 1);
lean_inc(v_snd_776_);
lean_dec_ref(v_____x_740_);
v_val_777_ = lean_ctor_get(v_fst_764_, 0);
lean_inc(v_val_777_);
lean_dec_ref_known(v_fst_764_, 1);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v_val_777_);
v___x_779_ = v___x_762_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_val_777_);
v___x_779_ = v_reuseFailAlloc_784_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_781_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v_snd_776_);
lean_ctor_set(v___x_766_, 0, v___x_779_);
v___x_781_ = v___x_766_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_snd_776_);
v___x_781_ = v_reuseFailAlloc_783_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; 
v___x_782_ = lean_apply_2(v_toPure_738_, lean_box(0), v___x_781_);
return v___x_782_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2(lean_object* v_toPure_788_, lean_object* v___x_789_, lean_object* v___x_790_, lean_object* v_____x_791_){
_start:
{
lean_object* v_fst_792_; 
v_fst_792_ = lean_ctor_get(v_____x_791_, 0);
lean_inc(v_fst_792_);
if (lean_obj_tag(v_fst_792_) == 0)
{
lean_object* v_snd_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v___x_789_);
v_snd_793_ = lean_ctor_get(v_____x_791_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v_____x_791_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v_____x_791_, 0);
lean_dec(v_unused_810_);
v___x_795_ = v_____x_791_;
v_isShared_796_ = v_isSharedCheck_809_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snd_793_);
lean_dec(v_____x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_809_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_808_; 
v_a_797_ = lean_ctor_get(v_fst_792_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v_fst_792_);
if (v_isSharedCheck_808_ == 0)
{
v___x_799_ = v_fst_792_;
v_isShared_800_ = v_isSharedCheck_808_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v_fst_792_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_808_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_807_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_804_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_802_);
v___x_804_ = v___x_795_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_snd_793_);
v___x_804_ = v_reuseFailAlloc_806_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_805_; 
v___x_805_ = lean_apply_2(v_toPure_788_, lean_box(0), v___x_804_);
return v___x_805_;
}
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_846_; 
v_a_811_ = lean_ctor_get(v_fst_792_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v_fst_792_);
if (v_isSharedCheck_846_ == 0)
{
v___x_813_ = v_fst_792_;
v_isShared_814_ = v_isSharedCheck_846_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v_fst_792_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_846_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
uint8_t v___x_815_; 
v___x_815_ = lean_unbox(v_a_811_);
lean_dec(v_a_811_);
if (v___x_815_ == 0)
{
lean_object* v_snd_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_828_; 
v_snd_816_ = lean_ctor_get(v_____x_791_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_____x_791_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; 
v_unused_829_ = lean_ctor_get(v_____x_791_, 0);
lean_dec(v_unused_829_);
v___x_818_ = v_____x_791_;
v_isShared_819_ = v_isSharedCheck_828_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_snd_816_);
lean_dec(v_____x_791_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_828_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_789_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_820_);
v___x_822_ = v___x_813_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_827_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_824_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_822_);
v___x_824_ = v___x_818_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_snd_816_);
v___x_824_ = v_reuseFailAlloc_826_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; 
v___x_825_ = lean_apply_2(v_toPure_788_, lean_box(0), v___x_824_);
return v___x_825_;
}
}
}
}
else
{
lean_object* v_snd_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref(v___x_789_);
v_snd_830_ = lean_ctor_get(v_____x_791_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_____x_791_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v_____x_791_, 0);
lean_dec(v_unused_845_);
v___x_832_ = v_____x_791_;
v_isShared_833_ = v_isSharedCheck_844_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_snd_830_);
lean_dec(v_____x_791_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_844_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_790_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v___x_790_);
lean_ctor_set(v___x_832_, 0, v___x_834_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v___x_790_);
v___x_836_ = v_reuseFailAlloc_843_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_837_);
v___x_839_ = v___x_813_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_842_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v_snd_830_);
v___x_841_ = lean_apply_2(v_toPure_788_, lean_box(0), v___x_840_);
return v___x_841_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(lean_object* v_inst_847_, lean_object* v_toBind_848_, lean_object* v___f_849_, lean_object* v_____r_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_847_, v___y_851_, v___y_852_);
v___x_854_ = lean_apply_4(v_toBind_848_, lean_box(0), lean_box(0), v___x_853_, v___f_849_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed(lean_object* v_inst_855_, lean_object* v_toBind_856_, lean_object* v___f_857_, lean_object* v_____r_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(v_inst_855_, v_toBind_856_, v___f_857_, v_____r_858_, v___y_859_, v___y_860_);
lean_dec_ref(v___y_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(lean_object* v_toPure_862_, lean_object* v_next_863_, lean_object* v_G_864_, lean_object* v___y_865_, lean_object* v_____x_866_){
_start:
{
lean_object* v_fst_867_; 
v_fst_867_ = lean_ctor_get(v_____x_866_, 0);
lean_inc(v_fst_867_);
if (lean_obj_tag(v_fst_867_) == 0)
{
lean_object* v_snd_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_884_; 
lean_dec(v_G_864_);
v_snd_868_ = lean_ctor_get(v_____x_866_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v_____x_866_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v_____x_866_, 0);
lean_dec(v_unused_885_);
v___x_870_ = v_____x_866_;
v_isShared_871_ = v_isSharedCheck_884_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_snd_868_);
lean_dec(v_____x_866_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_884_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_883_; 
v_a_872_ = lean_ctor_get(v_fst_867_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v_fst_867_);
if (v_isSharedCheck_883_ == 0)
{
v___x_874_ = v_fst_867_;
v_isShared_875_ = v_isSharedCheck_883_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v_fst_867_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_883_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_882_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_879_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_877_);
v___x_879_ = v___x_870_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_snd_868_);
v___x_879_ = v_reuseFailAlloc_881_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; 
v___x_880_ = lean_apply_2(v_toPure_862_, lean_box(0), v___x_879_);
return v___x_880_;
}
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_909_; 
v_a_886_ = lean_ctor_get(v_fst_867_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v_fst_867_);
if (v_isSharedCheck_909_ == 0)
{
v___x_888_ = v_fst_867_;
v_isShared_889_ = v_isSharedCheck_909_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v_fst_867_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_909_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
if (lean_obj_tag(v_a_886_) == 0)
{
lean_object* v_snd_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_902_; 
lean_dec(v_G_864_);
v_snd_890_ = lean_ctor_get(v_____x_866_, 1);
v_isSharedCheck_902_ = !lean_is_exclusive(v_____x_866_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v_____x_866_, 0);
lean_dec(v_unused_903_);
v___x_892_ = v_____x_866_;
v_isShared_893_ = v_isSharedCheck_902_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_snd_890_);
lean_dec(v_____x_866_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_902_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_a_894_; lean_object* v___x_896_; 
v_a_894_ = lean_ctor_get(v_a_886_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v_a_886_, 1);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v_a_894_);
v___x_896_ = v___x_888_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_894_);
v___x_896_ = v_reuseFailAlloc_901_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_898_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_896_);
v___x_898_ = v___x_892_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_snd_890_);
v___x_898_ = v_reuseFailAlloc_900_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; 
v___x_899_ = lean_apply_2(v_toPure_862_, lean_box(0), v___x_898_);
return v___x_899_;
}
}
}
}
else
{
lean_object* v_snd_904_; lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_del_object(v___x_888_);
lean_dec(v_toPure_862_);
v_snd_904_ = lean_ctor_get(v_____x_866_, 1);
lean_inc(v_snd_904_);
lean_dec_ref(v_____x_866_);
v_a_905_ = lean_ctor_get(v_a_886_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v_a_886_, 1);
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = lean_nat_add(v_next_863_, v___x_906_);
lean_inc_ref(v___y_865_);
v___x_908_ = lean_apply_6(v_G_864_, v___x_907_, v_a_905_, lean_box(0), lean_box(0), v___y_865_, v_snd_904_);
return v___x_908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed(lean_object* v_toPure_910_, lean_object* v_next_911_, lean_object* v_G_912_, lean_object* v___y_913_, lean_object* v_____x_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(v_toPure_910_, v_next_911_, v_G_912_, v___y_913_, v_____x_914_);
lean_dec_ref(v___y_913_);
lean_dec(v_next_911_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(lean_object* v_toPure_916_, lean_object* v___f_917_, lean_object* v___y_918_, lean_object* v_____x_919_){
_start:
{
lean_object* v_fst_920_; 
v_fst_920_ = lean_ctor_get(v_____x_919_, 0);
lean_inc(v_fst_920_);
if (lean_obj_tag(v_fst_920_) == 0)
{
lean_object* v_snd_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_937_; 
lean_dec(v___f_917_);
v_snd_921_ = lean_ctor_get(v_____x_919_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_____x_919_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v_____x_919_, 0);
lean_dec(v_unused_938_);
v___x_923_ = v_____x_919_;
v_isShared_924_ = v_isSharedCheck_937_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_snd_921_);
lean_dec(v_____x_919_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_937_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_936_; 
v_a_925_ = lean_ctor_get(v_fst_920_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v_fst_920_);
if (v_isSharedCheck_936_ == 0)
{
v___x_927_ = v_fst_920_;
v_isShared_928_ = v_isSharedCheck_936_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v_fst_920_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_936_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_935_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_932_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_930_);
v___x_932_ = v___x_923_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_snd_921_);
v___x_932_ = v_reuseFailAlloc_934_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; 
v___x_933_ = lean_apply_2(v_toPure_916_, lean_box(0), v___x_932_);
return v___x_933_;
}
}
}
}
}
else
{
lean_object* v_snd_939_; lean_object* v_a_940_; lean_object* v___x_941_; 
lean_dec(v_toPure_916_);
v_snd_939_ = lean_ctor_get(v_____x_919_, 1);
lean_inc(v_snd_939_);
lean_dec_ref(v_____x_919_);
v_a_940_ = lean_ctor_get(v_fst_920_, 0);
lean_inc(v_a_940_);
lean_dec_ref_known(v_fst_920_, 1);
lean_inc_ref(v___y_918_);
v___x_941_ = lean_apply_3(v___f_917_, v_a_940_, v___y_918_, v_snd_939_);
return v___x_941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed(lean_object* v_toPure_942_, lean_object* v___f_943_, lean_object* v___y_944_, lean_object* v_____x_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(v_toPure_942_, v___f_943_, v___y_944_, v_____x_945_);
lean_dec_ref(v___y_944_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(lean_object* v___x_947_, lean_object* v_toPure_948_, lean_object* v_toBind_949_, lean_object* v___f_950_, lean_object* v_initialMask_951_, lean_object* v___f_952_, lean_object* v_inst_953_, lean_object* v___x_954_, lean_object* v_next_955_, lean_object* v_acc_956_, lean_object* v_h_957_, lean_object* v_G_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v___x_961_; 
v___x_961_ = lean_nat_dec_lt(v_next_955_, v___x_947_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec(v_G_958_);
lean_dec(v_next_955_);
lean_dec_ref(v_inst_953_);
lean_dec(v___f_952_);
lean_dec(v___f_950_);
lean_dec(v_toBind_949_);
v___x_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_962_, 0, v_acc_956_);
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___y_960_);
v___x_964_ = lean_apply_2(v_toPure_948_, lean_box(0), v___x_963_);
return v___x_964_;
}
else
{
lean_object* v___f_965_; lean_object* v___y_967_; lean_object* v___x_970_; uint8_t v___x_971_; 
lean_dec_ref(v_acc_956_);
lean_inc_ref(v___y_959_);
lean_inc(v_next_955_);
lean_inc(v_toPure_948_);
v___f_965_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_965_, 0, v_toPure_948_);
lean_closure_set(v___f_965_, 1, v_next_955_);
lean_closure_set(v___f_965_, 2, v_G_958_);
lean_closure_set(v___f_965_, 3, v___y_959_);
v___x_970_ = lean_array_fget_borrowed(v_initialMask_951_, v_next_955_);
v___x_971_ = lean_unbox(v___x_970_);
if (v___x_971_ == 0)
{
lean_object* v___f_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
lean_inc_ref(v___y_959_);
v___f_972_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_972_, 0, v_toPure_948_);
lean_closure_set(v___f_972_, 1, v___f_952_);
lean_closure_set(v___f_972_, 2, v___y_959_);
v___x_973_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(v_next_955_, v_inst_953_, v___y_960_);
lean_inc(v_toBind_949_);
v___x_974_ = lean_apply_4(v_toBind_949_, lean_box(0), lean_box(0), v___x_973_, v___f_972_);
v___y_967_ = v___x_974_;
goto v___jp_966_;
}
else
{
lean_object* v___x_975_; 
lean_dec(v_next_955_);
lean_dec_ref(v_inst_953_);
lean_dec(v_toPure_948_);
lean_inc_ref(v___y_959_);
v___x_975_ = lean_apply_3(v___f_952_, v___x_954_, v___y_959_, v___y_960_);
v___y_967_ = v___x_975_;
goto v___jp_966_;
}
v___jp_966_:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
lean_inc(v_toBind_949_);
v___x_968_ = lean_apply_4(v_toBind_949_, lean_box(0), lean_box(0), v___y_967_, v___f_950_);
v___x_969_ = lean_apply_4(v_toBind_949_, lean_box(0), lean_box(0), v___x_968_, v___f_965_);
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed(lean_object* v___x_976_, lean_object* v_toPure_977_, lean_object* v_toBind_978_, lean_object* v___f_979_, lean_object* v_initialMask_980_, lean_object* v___f_981_, lean_object* v_inst_982_, lean_object* v___x_983_, lean_object* v_next_984_, lean_object* v_acc_985_, lean_object* v_h_986_, lean_object* v_G_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(v___x_976_, v_toPure_977_, v_toBind_978_, v___f_979_, v_initialMask_980_, v___f_981_, v_inst_982_, v___x_983_, v_next_984_, v_acc_985_, v_h_986_, v_G_987_, v___y_988_, v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec_ref(v_initialMask_980_);
lean_dec(v___x_976_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(lean_object* v_toPure_994_, lean_object* v_inst_995_, lean_object* v_toBind_996_, lean_object* v___f_997_, lean_object* v_a_998_, lean_object* v_____x_999_){
_start:
{
lean_object* v_fst_1000_; 
v_fst_1000_ = lean_ctor_get(v_____x_999_, 0);
lean_inc(v_fst_1000_);
if (lean_obj_tag(v_fst_1000_) == 0)
{
lean_object* v_snd_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v___f_997_);
lean_dec(v_toBind_996_);
lean_dec_ref(v_inst_995_);
v_snd_1001_ = lean_ctor_get(v_____x_999_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_____x_999_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v_____x_999_, 0);
lean_dec(v_unused_1018_);
v___x_1003_ = v_____x_999_;
v_isShared_1004_ = v_isSharedCheck_1017_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_snd_1001_);
lean_dec(v_____x_999_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1017_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1016_; 
v_a_1005_ = lean_ctor_get(v_fst_1000_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_fst_1000_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1007_ = v_fst_1000_;
v_isShared_1008_ = v_isSharedCheck_1016_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v_fst_1000_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1016_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1012_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1010_);
v___x_1012_ = v___x_1003_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_snd_1001_);
v___x_1012_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_apply_2(v_toPure_994_, lean_box(0), v___x_1012_);
return v___x_1013_;
}
}
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v_snd_1020_; lean_object* v_initialMask_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___x_6132__overap_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_a_1019_ = lean_ctor_get(v_fst_1000_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v_fst_1000_, 1);
v_snd_1020_ = lean_ctor_get(v_____x_999_, 1);
lean_inc(v_snd_1020_);
lean_dec_ref(v_____x_999_);
v_initialMask_1021_ = lean_ctor_get(v_a_1019_, 0);
lean_inc_ref(v_initialMask_1021_);
lean_dec(v_a_1019_);
v___x_1022_ = lean_array_get_size(v_initialMask_1021_);
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = lean_box(0);
lean_inc_n(v_toPure_994_, 2);
v___f_1025_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1025_, 0, v_toPure_994_);
lean_closure_set(v___f_1025_, 1, v___x_1024_);
v___x_1026_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0));
v___f_1027_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1027_, 0, v_toPure_994_);
lean_closure_set(v___f_1027_, 1, v___x_1026_);
lean_closure_set(v___f_1027_, 2, v___x_1024_);
lean_inc_n(v_toBind_996_, 2);
lean_inc_ref(v_inst_995_);
v___f_1028_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1028_, 0, v_inst_995_);
lean_closure_set(v___f_1028_, 1, v_toBind_996_);
lean_closure_set(v___f_1028_, 2, v___f_1027_);
v___f_1029_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed), 14, 8);
lean_closure_set(v___f_1029_, 0, v___x_1022_);
lean_closure_set(v___f_1029_, 1, v_toPure_994_);
lean_closure_set(v___f_1029_, 2, v_toBind_996_);
lean_closure_set(v___f_1029_, 3, v___f_997_);
lean_closure_set(v___f_1029_, 4, v_initialMask_1021_);
lean_closure_set(v___f_1029_, 5, v___f_1028_);
lean_closure_set(v___f_1029_, 6, v_inst_995_);
lean_closure_set(v___f_1029_, 7, v___x_1024_);
v___x_6132__overap_1030_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1029_, v___x_1023_, v___x_1026_, lean_box(0));
lean_inc_ref(v_a_998_);
v___x_1031_ = lean_apply_2(v___x_6132__overap_1030_, v_a_998_, v_snd_1020_);
v___x_1032_ = lean_apply_4(v_toBind_996_, lean_box(0), lean_box(0), v___x_1031_, v___f_1025_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed(lean_object* v_toPure_1033_, lean_object* v_inst_1034_, lean_object* v_toBind_1035_, lean_object* v___f_1036_, lean_object* v_a_1037_, lean_object* v_____x_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(v_toPure_1033_, v_inst_1034_, v_toBind_1035_, v___f_1036_, v_a_1037_, v_____x_1038_);
lean_dec_ref(v_a_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(lean_object* v_inst_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_toApplicative_1043_; lean_object* v_toBind_1044_; lean_object* v_toPure_1045_; lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_toApplicative_1043_ = lean_ctor_get(v_inst_1040_, 0);
v_toBind_1044_ = lean_ctor_get(v_inst_1040_, 1);
lean_inc_n(v_toBind_1044_, 2);
v_toPure_1045_ = lean_ctor_get(v_toApplicative_1043_, 1);
lean_inc_n(v_toPure_1045_, 3);
v___f_1046_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1046_, 0, v_toPure_1045_);
lean_inc_ref_n(v_a_1041_, 2);
v___f_1047_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_1047_, 0, v_toPure_1045_);
lean_closure_set(v___f_1047_, 1, v_inst_1040_);
lean_closure_set(v___f_1047_, 2, v_toBind_1044_);
lean_closure_set(v___f_1047_, 3, v___f_1046_);
lean_closure_set(v___f_1047_, 4, v_a_1041_);
v___x_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1048_, 0, v_a_1041_);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v_a_1042_);
v___x_1050_ = lean_apply_2(v_toPure_1045_, lean_box(0), v___x_1049_);
v___x_1051_ = lean_apply_4(v_toBind_1044_, lean_box(0), lean_box(0), v___x_1050_, v___f_1047_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___boxed(lean_object* v_inst_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1052_, v_a_1053_, v_a_1054_);
lean_dec_ref(v_a_1053_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(lean_object* v_m_1056_, lean_object* v_inst_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1057_, v_a_1058_, v_a_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___boxed(lean_object* v_m_1061_, lean_object* v_inst_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(v_m_1061_, v_inst_1062_, v_a_1063_, v_a_1064_);
lean_dec_ref(v_a_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0(lean_object* v_toPure_1068_, lean_object* v_____x_1069_){
_start:
{
lean_object* v_fst_1070_; 
v_fst_1070_ = lean_ctor_get(v_____x_1069_, 0);
lean_inc(v_fst_1070_);
if (lean_obj_tag(v_fst_1070_) == 0)
{
lean_object* v_snd_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1087_; 
v_snd_1071_ = lean_ctor_get(v_____x_1069_, 1);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_____x_1069_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v_____x_1069_, 0);
lean_dec(v_unused_1088_);
v___x_1073_ = v_____x_1069_;
v_isShared_1074_ = v_isSharedCheck_1087_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_snd_1071_);
lean_dec(v_____x_1069_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1087_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1086_; 
v_a_1075_ = lean_ctor_get(v_fst_1070_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_fst_1070_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1077_ = v_fst_1070_;
v_isShared_1078_ = v_isSharedCheck_1086_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v_fst_1070_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1086_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1082_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1080_);
v___x_1082_ = v___x_1073_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_snd_1071_);
v___x_1082_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_apply_2(v_toPure_1068_, lean_box(0), v___x_1082_);
return v___x_1083_;
}
}
}
}
}
else
{
lean_object* v_snd_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1098_; 
lean_dec_ref_known(v_fst_1070_, 1);
v_snd_1089_ = lean_ctor_get(v_____x_1069_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_____x_1069_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v_____x_1069_, 0);
lean_dec(v_unused_1099_);
v___x_1091_ = v_____x_1069_;
v_isShared_1092_ = v_isSharedCheck_1098_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_snd_1089_);
lean_dec(v_____x_1069_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1098_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1093_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0));
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1093_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_snd_1089_);
v___x_1095_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_apply_2(v_toPure_1068_, lean_box(0), v___x_1095_);
return v___x_1096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1(lean_object* v_toPure_1100_, lean_object* v_____x_1101_){
_start:
{
lean_object* v_fst_1102_; 
v_fst_1102_ = lean_ctor_get(v_____x_1101_, 0);
lean_inc(v_fst_1102_);
if (lean_obj_tag(v_fst_1102_) == 0)
{
lean_object* v_snd_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1119_; 
v_snd_1103_ = lean_ctor_get(v_____x_1101_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_____x_1101_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v_____x_1101_, 0);
lean_dec(v_unused_1120_);
v___x_1105_ = v_____x_1101_;
v_isShared_1106_ = v_isSharedCheck_1119_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_snd_1103_);
lean_dec(v_____x_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1119_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1118_; 
v_a_1107_ = lean_ctor_get(v_fst_1102_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_fst_1102_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1109_ = v_fst_1102_;
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v_fst_1102_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1112_);
v___x_1114_ = v___x_1105_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_snd_1103_);
v___x_1114_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_apply_2(v_toPure_1100_, lean_box(0), v___x_1114_);
return v___x_1115_;
}
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1167_; 
v_a_1121_ = lean_ctor_get(v_fst_1102_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_fst_1102_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1123_ = v_fst_1102_;
v_isShared_1124_ = v_isSharedCheck_1167_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v_fst_1102_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1167_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
if (lean_obj_tag(v_a_1121_) == 0)
{
lean_object* v_snd_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1144_; 
v_snd_1125_ = lean_ctor_get(v_____x_1101_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_____x_1101_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v_____x_1101_, 0);
lean_dec(v_unused_1145_);
v___x_1127_ = v_____x_1101_;
v_isShared_1128_ = v_isSharedCheck_1144_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_snd_1125_);
lean_dec(v_____x_1101_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1144_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1143_; 
v_a_1129_ = lean_ctor_get(v_a_1121_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_a_1121_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1131_ = v_a_1121_;
v_isShared_1132_ = v_isSharedCheck_1143_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v_a_1121_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1143_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set_tag(v___x_1131_, 1);
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1134_);
v___x_1136_ = v___x_1123_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1136_);
v___x_1138_ = v___x_1127_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_snd_1125_);
v___x_1138_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_apply_2(v_toPure_1100_, lean_box(0), v___x_1138_);
return v___x_1139_;
}
}
}
}
}
}
else
{
lean_object* v_snd_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1165_; 
v_snd_1146_ = lean_ctor_get(v_____x_1101_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_____x_1101_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v_____x_1101_, 0);
lean_dec(v_unused_1166_);
v___x_1148_ = v_____x_1101_;
v_isShared_1149_ = v_isSharedCheck_1165_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_snd_1146_);
lean_dec(v_____x_1101_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1165_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1164_; 
v_a_1150_ = lean_ctor_get(v_a_1121_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_a_1121_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1152_ = v_a_1121_;
v_isShared_1153_ = v_isSharedCheck_1164_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v_a_1121_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1164_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 0);
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1157_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1155_);
v___x_1157_ = v___x_1123_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1157_);
v___x_1159_ = v___x_1148_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_snd_1146_);
v___x_1159_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_apply_2(v_toPure_1100_, lean_box(0), v___x_1159_);
return v___x_1160_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2(lean_object* v_toPure_1168_, lean_object* v___x_1169_, lean_object* v_____x_1170_){
_start:
{
lean_object* v_fst_1171_; 
v_fst_1171_ = lean_ctor_get(v_____x_1170_, 0);
lean_inc(v_fst_1171_);
if (lean_obj_tag(v_fst_1171_) == 0)
{
lean_object* v_snd_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v___x_1169_);
v_snd_1172_ = lean_ctor_get(v_____x_1170_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_____x_1170_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v_____x_1170_, 0);
lean_dec(v_unused_1189_);
v___x_1174_ = v_____x_1170_;
v_isShared_1175_ = v_isSharedCheck_1188_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_snd_1172_);
lean_dec(v_____x_1170_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1188_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1187_; 
v_a_1176_ = lean_ctor_get(v_fst_1171_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_fst_1171_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1178_ = v_fst_1171_;
v_isShared_1179_ = v_isSharedCheck_1187_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v_fst_1171_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1187_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1183_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1181_);
v___x_1183_ = v___x_1174_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_snd_1172_);
v___x_1183_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_apply_2(v_toPure_1168_, lean_box(0), v___x_1183_);
return v___x_1184_;
}
}
}
}
}
else
{
lean_object* v_snd_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1207_; 
v_snd_1190_ = lean_ctor_get(v_____x_1170_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_____x_1170_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v_____x_1170_, 0);
lean_dec(v_unused_1208_);
v___x_1192_ = v_____x_1170_;
v_isShared_1193_ = v_isSharedCheck_1207_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_snd_1190_);
lean_dec(v_____x_1170_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1207_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1205_; 
v_isSharedCheck_1205_ = !lean_is_exclusive(v_fst_1171_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v_fst_1171_, 0);
lean_dec(v_unused_1206_);
v___x_1195_ = v_fst_1171_;
v_isShared_1196_ = v_isSharedCheck_1205_;
goto v_resetjp_1194_;
}
else
{
lean_dec(v_fst_1171_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1205_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1169_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1197_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1199_);
v___x_1201_ = v___x_1192_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_snd_1190_);
v___x_1201_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_apply_2(v_toPure_1168_, lean_box(0), v___x_1201_);
return v___x_1202_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(lean_object* v_toPure_1209_, lean_object* v___x_1210_, lean_object* v_inst_1211_, lean_object* v_toBind_1212_, lean_object* v___f_1213_, lean_object* v___x_1214_, lean_object* v_____x_1215_){
_start:
{
lean_object* v_fst_1216_; 
v_fst_1216_ = lean_ctor_get(v_____x_1215_, 0);
lean_inc(v_fst_1216_);
if (lean_obj_tag(v_fst_1216_) == 0)
{
lean_object* v_snd_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1233_; 
lean_dec(v___x_1214_);
lean_dec(v___f_1213_);
lean_dec(v_toBind_1212_);
lean_dec_ref(v_inst_1211_);
v_snd_1217_ = lean_ctor_get(v_____x_1215_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_____x_1215_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v_____x_1215_, 0);
lean_dec(v_unused_1234_);
v___x_1219_ = v_____x_1215_;
v_isShared_1220_ = v_isSharedCheck_1233_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_snd_1217_);
lean_dec(v_____x_1215_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1233_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1232_; 
v_a_1221_ = lean_ctor_get(v_fst_1216_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_fst_1216_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1223_ = v_fst_1216_;
v_isShared_1224_ = v_isSharedCheck_1232_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v_fst_1216_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1232_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1228_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1226_);
v___x_1228_ = v___x_1219_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_snd_1217_);
v___x_1228_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_apply_2(v_toPure_1209_, lean_box(0), v___x_1228_);
return v___x_1229_;
}
}
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1257_; 
v_a_1235_ = lean_ctor_get(v_fst_1216_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_fst_1216_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1237_ = v_fst_1216_;
v_isShared_1238_ = v_isSharedCheck_1257_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v_fst_1216_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1257_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_unbox(v_a_1235_);
lean_dec(v_a_1235_);
if (v___x_1239_ == 0)
{
lean_object* v_snd_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_del_object(v___x_1237_);
lean_dec(v___x_1214_);
lean_dec(v_toPure_1209_);
v_snd_1240_ = lean_ctor_get(v_____x_1215_, 1);
lean_inc(v_snd_1240_);
lean_dec_ref(v_____x_1215_);
v___x_1241_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v___x_1210_, v_inst_1211_, v_snd_1240_);
v___x_1242_ = lean_apply_4(v_toBind_1212_, lean_box(0), lean_box(0), v___x_1241_, v___f_1213_);
return v___x_1242_;
}
else
{
lean_object* v_snd_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v___f_1213_);
lean_dec(v_toBind_1212_);
lean_dec_ref(v_inst_1211_);
v_snd_1243_ = lean_ctor_get(v_____x_1215_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_____x_1215_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v_____x_1215_, 0);
lean_dec(v_unused_1256_);
v___x_1245_ = v_____x_1215_;
v_isShared_1246_ = v_isSharedCheck_1255_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_snd_1243_);
lean_dec(v_____x_1215_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1255_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1214_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1247_);
v___x_1249_ = v___x_1237_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1251_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1249_);
v___x_1251_ = v___x_1245_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_snd_1243_);
v___x_1251_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_apply_2(v_toPure_1209_, lean_box(0), v___x_1251_);
return v___x_1252_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed(lean_object* v_toPure_1258_, lean_object* v___x_1259_, lean_object* v_inst_1260_, lean_object* v_toBind_1261_, lean_object* v___f_1262_, lean_object* v___x_1263_, lean_object* v_____x_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(v_toPure_1258_, v___x_1259_, v_inst_1260_, v_toBind_1261_, v___f_1262_, v___x_1263_, v_____x_1264_);
lean_dec(v___x_1259_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(lean_object* v_toPure_1266_, lean_object* v_inst_1267_, lean_object* v___y_1268_, lean_object* v_toBind_1269_, lean_object* v___f_1270_, lean_object* v_____x_1271_){
_start:
{
lean_object* v_fst_1272_; 
v_fst_1272_ = lean_ctor_get(v_____x_1271_, 0);
lean_inc(v_fst_1272_);
if (lean_obj_tag(v_fst_1272_) == 0)
{
lean_object* v_snd_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v___f_1270_);
lean_dec(v_toBind_1269_);
lean_dec_ref(v_inst_1267_);
v_snd_1273_ = lean_ctor_get(v_____x_1271_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_____x_1271_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v_____x_1271_, 0);
lean_dec(v_unused_1290_);
v___x_1275_ = v_____x_1271_;
v_isShared_1276_ = v_isSharedCheck_1289_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_snd_1273_);
lean_dec(v_____x_1271_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1289_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1288_; 
v_a_1277_ = lean_ctor_get(v_fst_1272_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_fst_1272_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1279_ = v_fst_1272_;
v_isShared_1280_ = v_isSharedCheck_1288_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v_fst_1272_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1288_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1284_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1282_);
v___x_1284_ = v___x_1275_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_snd_1273_);
v___x_1284_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_apply_2(v_toPure_1266_, lean_box(0), v___x_1284_);
return v___x_1285_;
}
}
}
}
}
else
{
lean_object* v_snd_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_dec_ref_known(v_fst_1272_, 1);
lean_dec(v_toPure_1266_);
v_snd_1291_ = lean_ctor_get(v_____x_1271_, 1);
lean_inc(v_snd_1291_);
lean_dec_ref(v_____x_1271_);
v___x_1292_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_1267_, v___y_1268_, v_snd_1291_);
v___x_1293_ = lean_apply_4(v_toBind_1269_, lean_box(0), lean_box(0), v___x_1292_, v___f_1270_);
return v___x_1293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed(lean_object* v_toPure_1294_, lean_object* v_inst_1295_, lean_object* v___y_1296_, lean_object* v_toBind_1297_, lean_object* v___f_1298_, lean_object* v_____x_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(v_toPure_1294_, v_inst_1295_, v___y_1296_, v_toBind_1297_, v___f_1298_, v_____x_1299_);
lean_dec_ref(v___y_1296_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(lean_object* v_toPure_1301_, lean_object* v___x_1302_, lean_object* v___x_1303_, lean_object* v_inst_1304_, lean_object* v_toBind_1305_, lean_object* v___f_1306_, lean_object* v___y_1307_, lean_object* v_____x_1308_){
_start:
{
lean_object* v_fst_1309_; 
v_fst_1309_ = lean_ctor_get(v_____x_1308_, 0);
lean_inc(v_fst_1309_);
if (lean_obj_tag(v_fst_1309_) == 0)
{
lean_object* v_snd_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v___f_1306_);
lean_dec(v_toBind_1305_);
lean_dec_ref(v_inst_1304_);
lean_dec(v___x_1303_);
v_snd_1310_ = lean_ctor_get(v_____x_1308_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_____x_1308_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v_____x_1308_, 0);
lean_dec(v_unused_1327_);
v___x_1312_ = v_____x_1308_;
v_isShared_1313_ = v_isSharedCheck_1326_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_snd_1310_);
lean_dec(v_____x_1308_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1326_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1325_; 
v_a_1314_ = lean_ctor_get(v_fst_1309_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_fst_1309_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1316_ = v_fst_1309_;
v_isShared_1317_ = v_isSharedCheck_1325_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v_fst_1309_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1325_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1321_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1319_);
v___x_1321_ = v___x_1312_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_snd_1310_);
v___x_1321_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_apply_2(v_toPure_1301_, lean_box(0), v___x_1321_);
return v___x_1322_;
}
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v_snd_1329_; lean_object* v_added_1330_; lean_object* v___x_1331_; lean_object* v___f_1332_; lean_object* v___f_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v_a_1328_ = lean_ctor_get(v_fst_1309_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v_fst_1309_, 1);
v_snd_1329_ = lean_ctor_get(v_____x_1308_, 1);
lean_inc(v_snd_1329_);
lean_dec_ref(v_____x_1308_);
v_added_1330_ = lean_ctor_get(v_a_1328_, 1);
lean_inc_ref(v_added_1330_);
lean_dec(v_a_1328_);
v___x_1331_ = lean_array_get(v___x_1302_, v_added_1330_, v___x_1303_);
lean_dec_ref(v_added_1330_);
lean_inc_n(v_toBind_1305_, 2);
lean_inc_ref_n(v_inst_1304_, 2);
lean_inc(v___x_1331_);
lean_inc(v_toPure_1301_);
v___f_1332_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1332_, 0, v_toPure_1301_);
lean_closure_set(v___f_1332_, 1, v___x_1331_);
lean_closure_set(v___f_1332_, 2, v_inst_1304_);
lean_closure_set(v___f_1332_, 3, v_toBind_1305_);
lean_closure_set(v___f_1332_, 4, v___f_1306_);
lean_closure_set(v___f_1332_, 5, v___x_1303_);
lean_inc_ref(v___y_1307_);
v___f_1333_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_1333_, 0, v_toPure_1301_);
lean_closure_set(v___f_1333_, 1, v_inst_1304_);
lean_closure_set(v___f_1333_, 2, v___y_1307_);
lean_closure_set(v___f_1333_, 3, v_toBind_1305_);
lean_closure_set(v___f_1333_, 4, v___f_1332_);
v___x_1334_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v___x_1331_, v_inst_1304_, v_snd_1329_);
lean_dec(v___x_1331_);
v___x_1335_ = lean_apply_4(v_toBind_1305_, lean_box(0), lean_box(0), v___x_1334_, v___f_1333_);
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed(lean_object* v_toPure_1336_, lean_object* v___x_1337_, lean_object* v___x_1338_, lean_object* v_inst_1339_, lean_object* v_toBind_1340_, lean_object* v___f_1341_, lean_object* v___y_1342_, lean_object* v_____x_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(v_toPure_1336_, v___x_1337_, v___x_1338_, v_inst_1339_, v_toBind_1340_, v___f_1341_, v___y_1342_, v_____x_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___x_1337_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7(lean_object* v_toPure_1345_, lean_object* v_toBind_1346_, lean_object* v___f_1347_, lean_object* v___x_1348_, lean_object* v___x_1349_, lean_object* v_inst_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_nat_dec_lt(v___x_1354_, v_b_1351_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec_ref(v_inst_1350_);
lean_dec(v___x_1349_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_b_1351_);
v___x_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___y_1353_);
v___x_1359_ = lean_apply_2(v_toPure_1345_, lean_box(0), v___x_1358_);
v___x_1360_ = lean_apply_4(v_toBind_1346_, lean_box(0), lean_box(0), v___x_1359_, v___f_1347_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; lean_object* v___f_1362_; lean_object* v___f_1363_; lean_object* v___f_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1361_ = lean_nat_sub(v_b_1351_, v___x_1348_);
lean_dec(v_b_1351_);
lean_inc(v___x_1361_);
lean_inc_n(v_toPure_1345_, 3);
v___f_1362_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1362_, 0, v_toPure_1345_);
lean_closure_set(v___f_1362_, 1, v___x_1361_);
lean_inc_ref(v___y_1352_);
lean_inc_n(v_toBind_1346_, 3);
v___f_1363_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1363_, 0, v_toPure_1345_);
lean_closure_set(v___f_1363_, 1, v___x_1349_);
lean_closure_set(v___f_1363_, 2, v___x_1361_);
lean_closure_set(v___f_1363_, 3, v_inst_1350_);
lean_closure_set(v___f_1363_, 4, v_toBind_1346_);
lean_closure_set(v___f_1363_, 5, v___f_1362_);
lean_closure_set(v___f_1363_, 6, v___y_1352_);
v___f_1364_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1364_, 0, v_toPure_1345_);
lean_inc_ref(v___y_1353_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___y_1353_);
lean_ctor_set(v___x_1365_, 1, v___y_1353_);
v___x_1366_ = lean_apply_2(v_toPure_1345_, lean_box(0), v___x_1365_);
v___x_1367_ = lean_apply_4(v_toBind_1346_, lean_box(0), lean_box(0), v___x_1366_, v___f_1364_);
v___x_1368_ = lean_apply_4(v_toBind_1346_, lean_box(0), lean_box(0), v___x_1367_, v___f_1363_);
v___x_1369_ = lean_apply_4(v_toBind_1346_, lean_box(0), lean_box(0), v___x_1368_, v___f_1347_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed(lean_object* v_toPure_1370_, lean_object* v_toBind_1371_, lean_object* v___f_1372_, lean_object* v___x_1373_, lean_object* v___x_1374_, lean_object* v_inst_1375_, lean_object* v_b_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7(v_toPure_1370_, v_toBind_1371_, v___f_1372_, v___x_1373_, v___x_1374_, v_inst_1375_, v_b_1376_, v___y_1377_, v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___x_1373_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(lean_object* v_toPure_1380_, lean_object* v_toBind_1381_, lean_object* v___f_1382_, lean_object* v___x_1383_, lean_object* v_inst_1384_, lean_object* v___x_1385_, lean_object* v_a_1386_, lean_object* v___f_1387_, lean_object* v_____x_1388_){
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
lean_dec(v___x_1383_);
lean_dec(v___f_1382_);
lean_dec(v_toBind_1381_);
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
v___x_1402_ = lean_apply_2(v_toPure_1380_, lean_box(0), v___x_1401_);
return v___x_1402_;
}
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v_snd_1409_; lean_object* v_added_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___f_1413_; lean_object* v___x_1414_; lean_object* v___x_5974__overap_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
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
lean_inc(v_toBind_1381_);
v___f_1413_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed), 9, 6);
lean_closure_set(v___f_1413_, 0, v_toPure_1380_);
lean_closure_set(v___f_1413_, 1, v_toBind_1381_);
lean_closure_set(v___f_1413_, 2, v___f_1382_);
lean_closure_set(v___f_1413_, 3, v___x_1412_);
lean_closure_set(v___f_1413_, 4, v___x_1383_);
lean_closure_set(v___f_1413_, 5, v_inst_1384_);
v___x_1414_ = lean_nat_sub(v___x_1411_, v___x_1412_);
v___x_5974__overap_1415_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_1385_, v___f_1413_, v___x_1414_);
lean_inc_ref(v_a_1386_);
v___x_1416_ = lean_apply_2(v___x_5974__overap_1415_, v_a_1386_, v_snd_1409_);
v___x_1417_ = lean_apply_4(v_toBind_1381_, lean_box(0), lean_box(0), v___x_1416_, v___f_1387_);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed(lean_object* v_toPure_1418_, lean_object* v_toBind_1419_, lean_object* v___f_1420_, lean_object* v___x_1421_, lean_object* v_inst_1422_, lean_object* v___x_1423_, lean_object* v_a_1424_, lean_object* v___f_1425_, lean_object* v_____x_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(v_toPure_1418_, v_toBind_1419_, v___f_1420_, v___x_1421_, v_inst_1422_, v___x_1423_, v_a_1424_, v___f_1425_, v_____x_1426_);
lean_dec_ref(v_a_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(lean_object* v_inst_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v___f_1431_; lean_object* v___f_1432_; lean_object* v___f_1433_; lean_object* v___f_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___f_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v_toApplicative_1452_; lean_object* v_toBind_1453_; lean_object* v_toPure_1454_; lean_object* v___f_1455_; lean_object* v___f_1456_; lean_object* v___x_1457_; lean_object* v___f_1458_; lean_object* v___f_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_inc_ref_n(v_inst_1428_, 7);
v___f_1431_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1431_, 0, v_inst_1428_);
v___f_1432_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1432_, 0, v_inst_1428_);
v___f_1433_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1433_, 0, v_inst_1428_);
v___f_1434_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1434_, 0, v_inst_1428_);
v___x_1435_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1435_, 0, lean_box(0));
lean_closure_set(v___x_1435_, 1, lean_box(0));
lean_closure_set(v___x_1435_, 2, v_inst_1428_);
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v___f_1431_);
v___x_1437_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1437_, 0, lean_box(0));
lean_closure_set(v___x_1437_, 1, lean_box(0));
lean_closure_set(v___x_1437_, 2, v_inst_1428_);
v___x_1438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1436_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
lean_ctor_set(v___x_1438_, 2, v___f_1432_);
lean_ctor_set(v___x_1438_, 3, v___f_1433_);
lean_ctor_set(v___x_1438_, 4, v___f_1434_);
v___x_1439_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1439_, 0, lean_box(0));
lean_closure_set(v___x_1439_, 1, lean_box(0));
lean_closure_set(v___x_1439_, 2, v_inst_1428_);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1438_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
lean_inc_ref_n(v___x_1440_, 6);
v___f_1441_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1441_, 0, v___x_1440_);
v___f_1442_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1442_, 0, v___x_1440_);
v___f_1443_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1443_, 0, v___x_1440_);
v___f_1444_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1444_, 0, v___x_1440_);
v___x_1445_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1445_, 0, lean_box(0));
lean_closure_set(v___x_1445_, 1, lean_box(0));
lean_closure_set(v___x_1445_, 2, v___x_1440_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v___f_1441_);
v___x_1447_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1447_, 0, lean_box(0));
lean_closure_set(v___x_1447_, 1, lean_box(0));
lean_closure_set(v___x_1447_, 2, v___x_1440_);
v___x_1448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1446_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
lean_ctor_set(v___x_1448_, 2, v___f_1442_);
lean_ctor_set(v___x_1448_, 3, v___f_1443_);
lean_ctor_set(v___x_1448_, 4, v___f_1444_);
v___x_1449_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1449_, 0, lean_box(0));
lean_closure_set(v___x_1449_, 1, lean_box(0));
lean_closure_set(v___x_1449_, 2, v___x_1440_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1448_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = l_ReaderT_instMonad___redArg(v___x_1450_);
v_toApplicative_1452_ = lean_ctor_get(v_inst_1428_, 0);
v_toBind_1453_ = lean_ctor_get(v_inst_1428_, 1);
lean_inc_n(v_toBind_1453_, 3);
v_toPure_1454_ = lean_ctor_get(v_toApplicative_1452_, 1);
lean_inc_n(v_toPure_1454_, 5);
v___f_1455_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1455_, 0, v_toPure_1454_);
v___f_1456_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1456_, 0, v_toPure_1454_);
v___x_1457_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1429_);
v___f_1458_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed), 9, 8);
lean_closure_set(v___f_1458_, 0, v_toPure_1454_);
lean_closure_set(v___f_1458_, 1, v_toBind_1453_);
lean_closure_set(v___f_1458_, 2, v___f_1456_);
lean_closure_set(v___f_1458_, 3, v___x_1457_);
lean_closure_set(v___f_1458_, 4, v_inst_1428_);
lean_closure_set(v___f_1458_, 5, v___x_1451_);
lean_closure_set(v___f_1458_, 6, v_a_1429_);
lean_closure_set(v___f_1458_, 7, v___f_1455_);
v___f_1459_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1459_, 0, v_toPure_1454_);
lean_inc_ref(v_a_1430_);
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v_a_1430_);
lean_ctor_set(v___x_1460_, 1, v_a_1430_);
v___x_1461_ = lean_apply_2(v_toPure_1454_, lean_box(0), v___x_1460_);
v___x_1462_ = lean_apply_4(v_toBind_1453_, lean_box(0), lean_box(0), v___x_1461_, v___f_1459_);
v___x_1463_ = lean_apply_4(v_toBind_1453_, lean_box(0), lean_box(0), v___x_1462_, v___f_1458_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___boxed(lean_object* v_inst_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1464_, v_a_1465_, v_a_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(lean_object* v_m_1468_, lean_object* v_inst_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1469_, v_a_1470_, v_a_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___boxed(lean_object* v_m_1473_, lean_object* v_inst_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(v_m_1473_, v_inst_1474_, v_a_1475_, v_a_1476_);
lean_dec_ref(v_a_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(lean_object* v_toApplicative_1478_, lean_object* v_inst_1479_, lean_object* v_a_1480_, lean_object* v_____x_1481_){
_start:
{
lean_object* v_fst_1482_; 
v_fst_1482_ = lean_ctor_get(v_____x_1481_, 0);
lean_inc(v_fst_1482_);
if (lean_obj_tag(v_fst_1482_) == 0)
{
lean_object* v_snd_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1500_; 
lean_dec_ref(v_inst_1479_);
v_snd_1483_ = lean_ctor_get(v_____x_1481_, 1);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_____x_1481_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v_____x_1481_, 0);
lean_dec(v_unused_1501_);
v___x_1485_ = v_____x_1481_;
v_isShared_1486_ = v_isSharedCheck_1500_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_snd_1483_);
lean_dec(v_____x_1481_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1500_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1499_; 
v_a_1487_ = lean_ctor_get(v_fst_1482_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_fst_1482_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1489_ = v_fst_1482_;
v_isShared_1490_ = v_isSharedCheck_1499_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v_fst_1482_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1499_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v_toPure_1491_; lean_object* v___x_1493_; 
v_toPure_1491_ = lean_ctor_get(v_toApplicative_1478_, 1);
lean_inc(v_toPure_1491_);
lean_dec_ref(v_toApplicative_1478_);
if (v_isShared_1490_ == 0)
{
v___x_1493_ = v___x_1489_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1487_);
v___x_1493_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1493_);
v___x_1495_ = v___x_1485_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_snd_1483_);
v___x_1495_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_apply_2(v_toPure_1491_, lean_box(0), v___x_1495_);
return v___x_1496_;
}
}
}
}
}
else
{
lean_object* v_a_1502_; uint8_t v_found_1503_; 
v_a_1502_ = lean_ctor_get(v_fst_1482_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v_fst_1482_, 1);
v_found_1503_ = lean_ctor_get_uint8(v_a_1502_, sizeof(void*)*3);
lean_dec(v_a_1502_);
if (v_found_1503_ == 0)
{
lean_object* v_snd_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1514_; 
lean_dec_ref(v_inst_1479_);
v_snd_1504_ = lean_ctor_get(v_____x_1481_, 1);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_____x_1481_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v_____x_1481_, 0);
lean_dec(v_unused_1515_);
v___x_1506_ = v_____x_1481_;
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_snd_1504_);
lean_dec(v_____x_1481_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v_toPure_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v_toPure_1508_ = lean_ctor_get(v_toApplicative_1478_, 1);
lean_inc(v_toPure_1508_);
lean_dec_ref(v_toApplicative_1478_);
v___x_1509_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0));
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1509_);
v___x_1511_ = v___x_1506_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_snd_1504_);
v___x_1511_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_apply_2(v_toPure_1508_, lean_box(0), v___x_1511_);
return v___x_1512_;
}
}
}
else
{
lean_object* v_snd_1516_; lean_object* v___x_1517_; 
lean_dec_ref(v_toApplicative_1478_);
v_snd_1516_ = lean_ctor_get(v_____x_1481_, 1);
lean_inc(v_snd_1516_);
lean_dec_ref(v_____x_1481_);
v___x_1517_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1479_, v_a_1480_, v_snd_1516_);
return v___x_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed(lean_object* v_toApplicative_1518_, lean_object* v_inst_1519_, lean_object* v_a_1520_, lean_object* v_____x_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(v_toApplicative_1518_, v_inst_1519_, v_a_1520_, v_____x_1521_);
lean_dec_ref(v_a_1520_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2(lean_object* v_toApplicative_1523_, lean_object* v_toBind_1524_, lean_object* v___f_1525_, lean_object* v_____x_1526_){
_start:
{
lean_object* v_fst_1527_; 
v_fst_1527_ = lean_ctor_get(v_____x_1526_, 0);
if (lean_obj_tag(v_fst_1527_) == 0)
{
lean_object* v_toPure_1528_; lean_object* v___x_1529_; 
lean_dec(v___f_1525_);
lean_dec(v_toBind_1524_);
v_toPure_1528_ = lean_ctor_get(v_toApplicative_1523_, 1);
lean_inc(v_toPure_1528_);
lean_dec_ref(v_toApplicative_1523_);
v___x_1529_ = lean_apply_2(v_toPure_1528_, lean_box(0), v_____x_1526_);
return v___x_1529_;
}
else
{
lean_object* v_snd_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1542_; 
v_snd_1530_ = lean_ctor_get(v_____x_1526_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_____x_1526_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v_____x_1526_, 0);
lean_dec(v_unused_1543_);
v___x_1532_ = v_____x_1526_;
v_isShared_1533_ = v_isSharedCheck_1542_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_snd_1530_);
lean_dec(v_____x_1526_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1542_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v_toPure_1534_; lean_object* v___f_1535_; lean_object* v___x_1537_; 
v_toPure_1534_ = lean_ctor_get(v_toApplicative_1523_, 1);
lean_inc_n(v_toPure_1534_, 2);
lean_dec_ref(v_toApplicative_1523_);
v___f_1535_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1535_, 0, v_toPure_1534_);
lean_inc(v_snd_1530_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v_snd_1530_);
v___x_1537_ = v___x_1532_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_snd_1530_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_snd_1530_);
v___x_1537_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = lean_apply_2(v_toPure_1534_, lean_box(0), v___x_1537_);
lean_inc(v_toBind_1524_);
v___x_1539_ = lean_apply_4(v_toBind_1524_, lean_box(0), lean_box(0), v___x_1538_, v___f_1535_);
v___x_1540_ = lean_apply_4(v_toBind_1524_, lean_box(0), lean_box(0), v___x_1539_, v___f_1525_);
return v___x_1540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(lean_object* v_inst_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_toApplicative_1547_; lean_object* v_toBind_1548_; lean_object* v___f_1549_; lean_object* v___f_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_toApplicative_1547_ = lean_ctor_get(v_inst_1544_, 0);
v_toBind_1548_ = lean_ctor_get(v_inst_1544_, 1);
lean_inc_n(v_toBind_1548_, 2);
lean_inc_ref(v_a_1545_);
lean_inc_ref(v_inst_1544_);
lean_inc_ref_n(v_toApplicative_1547_, 2);
v___f_1549_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1549_, 0, v_toApplicative_1547_);
lean_closure_set(v___f_1549_, 1, v_inst_1544_);
lean_closure_set(v___f_1549_, 2, v_a_1545_);
v___f_1550_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1550_, 0, v_toApplicative_1547_);
lean_closure_set(v___f_1550_, 1, v_toBind_1548_);
lean_closure_set(v___f_1550_, 2, v___f_1549_);
v___x_1551_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1544_, v_a_1545_, v_a_1546_);
v___x_1552_ = lean_apply_4(v_toBind_1548_, lean_box(0), lean_box(0), v___x_1551_, v___f_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___boxed(lean_object* v_inst_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1553_, v_a_1554_, v_a_1555_);
lean_dec_ref(v_a_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(lean_object* v_m_1557_, lean_object* v_inst_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1558_, v_a_1559_, v_a_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___boxed(lean_object* v_m_1562_, lean_object* v_inst_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(v_m_1562_, v_inst_1563_, v_a_1564_, v_a_1565_);
lean_dec_ref(v_a_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0(lean_object* v_toPure_1567_, lean_object* v_____x_1568_){
_start:
{
lean_object* v_snd_1569_; lean_object* v_fst_1570_; lean_object* v_cur_1571_; lean_object* v_numCalls_1572_; uint8_t v_found_1573_; uint8_t v___y_1575_; 
v_snd_1569_ = lean_ctor_get(v_____x_1568_, 1);
v_fst_1570_ = lean_ctor_get(v_____x_1568_, 0);
v_cur_1571_ = lean_ctor_get(v_snd_1569_, 0);
v_numCalls_1572_ = lean_ctor_get(v_snd_1569_, 2);
v_found_1573_ = lean_ctor_get_uint8(v_snd_1569_, sizeof(void*)*3);
if (v_found_1573_ == 0)
{
uint8_t v___x_1578_; 
v___x_1578_ = 0;
v___y_1575_ = v___x_1578_;
goto v___jp_1574_;
}
else
{
if (lean_obj_tag(v_fst_1570_) == 0)
{
uint8_t v___x_1579_; 
v___x_1579_ = 1;
v___y_1575_ = v___x_1579_;
goto v___jp_1574_;
}
else
{
uint8_t v___x_1580_; 
v___x_1580_ = 2;
v___y_1575_ = v___x_1580_;
goto v___jp_1574_;
}
}
v___jp_1574_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_inc(v_numCalls_1572_);
lean_inc_ref(v_cur_1571_);
v___x_1576_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1576_, 0, v_cur_1571_);
lean_ctor_set(v___x_1576_, 1, v_numCalls_1572_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*2, v___y_1575_);
v___x_1577_ = lean_apply_2(v_toPure_1567_, lean_box(0), v___x_1576_);
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed(lean_object* v_toPure_1581_, lean_object* v_____x_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__0(v_toPure_1581_, v_____x_1582_);
lean_dec_ref(v_____x_1582_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1(lean_object* v_initialMask_1586_, lean_object* v_test_1587_, lean_object* v_maxCalls_1588_, lean_object* v_inst_1589_, lean_object* v_toBind_1590_, lean_object* v___f_1591_, lean_object* v_toPure_1592_, uint8_t v_____do__lift_1593_){
_start:
{
if (v_____do__lift_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec(v_toPure_1592_);
lean_inc_ref(v_initialMask_1586_);
v___x_1594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1594_, 0, v_initialMask_1586_);
lean_ctor_set(v___x_1594_, 1, v_test_1587_);
lean_ctor_set(v___x_1594_, 2, v_maxCalls_1588_);
v___x_1595_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0));
v___x_1596_ = lean_unsigned_to_nat(1u);
v___x_1597_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1597_, 0, v_initialMask_1586_);
lean_ctor_set(v___x_1597_, 1, v___x_1595_);
lean_ctor_set(v___x_1597_, 2, v___x_1596_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*3, v_____do__lift_1593_);
v___x_1598_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1589_, v___x_1594_, v___x_1597_);
lean_dec_ref_known(v___x_1594_, 3);
v___x_1599_ = lean_apply_4(v_toBind_1590_, lean_box(0), lean_box(0), v___x_1598_, v___f_1591_);
return v___x_1599_;
}
else
{
uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v___f_1591_);
lean_dec(v_toBind_1590_);
lean_dec_ref(v_inst_1589_);
lean_dec(v_maxCalls_1588_);
lean_dec(v_test_1587_);
v___x_1600_ = 2;
v___x_1601_ = lean_unsigned_to_nat(1u);
v___x_1602_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1602_, 0, v_initialMask_1586_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*2, v___x_1600_);
v___x_1603_ = lean_apply_2(v_toPure_1592_, lean_box(0), v___x_1602_);
return v___x_1603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed(lean_object* v_initialMask_1604_, lean_object* v_test_1605_, lean_object* v_maxCalls_1606_, lean_object* v_inst_1607_, lean_object* v_toBind_1608_, lean_object* v___f_1609_, lean_object* v_toPure_1610_, lean_object* v_____do__lift_1611_){
_start:
{
uint8_t v_____do__lift_163__boxed_1612_; lean_object* v_res_1613_; 
v_____do__lift_163__boxed_1612_ = lean_unbox(v_____do__lift_1611_);
v_res_1613_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__1(v_initialMask_1604_, v_test_1605_, v_maxCalls_1606_, v_inst_1607_, v_toBind_1608_, v___f_1609_, v_toPure_1610_, v_____do__lift_163__boxed_1612_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg(lean_object* v_inst_1614_, lean_object* v_initialMask_1615_, lean_object* v_test_1616_, lean_object* v_maxCalls_1617_){
_start:
{
lean_object* v_toApplicative_1618_; lean_object* v_toBind_1619_; lean_object* v_toPure_1620_; lean_object* v___x_1621_; lean_object* v___f_1622_; lean_object* v___f_1623_; lean_object* v___x_1624_; 
v_toApplicative_1618_ = lean_ctor_get(v_inst_1614_, 0);
v_toBind_1619_ = lean_ctor_get(v_inst_1614_, 1);
lean_inc_n(v_toBind_1619_, 2);
v_toPure_1620_ = lean_ctor_get(v_toApplicative_1618_, 1);
lean_inc_n(v_toPure_1620_, 2);
lean_inc(v_test_1616_);
lean_inc_ref(v_initialMask_1615_);
v___x_1621_ = lean_apply_1(v_test_1616_, v_initialMask_1615_);
v___f_1622_ = lean_alloc_closure((void*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1622_, 0, v_toPure_1620_);
v___f_1623_ = lean_alloc_closure((void*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1623_, 0, v_initialMask_1615_);
lean_closure_set(v___f_1623_, 1, v_test_1616_);
lean_closure_set(v___f_1623_, 2, v_maxCalls_1617_);
lean_closure_set(v___f_1623_, 3, v_inst_1614_);
lean_closure_set(v___f_1623_, 4, v_toBind_1619_);
lean_closure_set(v___f_1623_, 5, v___f_1622_);
lean_closure_set(v___f_1623_, 6, v_toPure_1620_);
v___x_1624_ = lean_apply_4(v_toBind_1619_, lean_box(0), lean_box(0), v___x_1621_, v___f_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search(lean_object* v_m_1625_, lean_object* v_inst_1626_, lean_object* v_initialMask_1627_, lean_object* v_test_1628_, lean_object* v_maxCalls_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Util_ParamMinimizer_search___redArg(v_inst_1626_, v_initialMask_1627_, v_test_1628_, v_maxCalls_1629_);
return v___x_1630_;
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
