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
lean_object* l_Lean_Util_ParamMinimizer_Status_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Util_ParamMinimizer_Status_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Util_ParamMinimizer_Status_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Util_ParamMinimizer_Status_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Util_ParamMinimizer_Status_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Util_ParamMinimizer_Status_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Util_ParamMinimizer_Status_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg(lean_object* v_missing_24_){
_start:
{
lean_inc(v_missing_24_);
return v_missing_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg___boxed(lean_object* v_missing_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg(v_missing_25_);
lean_dec(v_missing_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_missing_30_){
_start:
{
lean_inc(v_missing_30_);
return v_missing_30_;
}
}
LEAN_EXPORT void l_Lean_Util_ParamMinimizer_Status_missing_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_missing_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Util_ParamMinimizer_Status_missing_elim(lean_box(0), v_t_28_, lean_box(0), v_missing_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_missing_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_missing_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Util_ParamMinimizer_Status_missing_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_missing_35_);
lean_dec(v_missing_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg(lean_object* v_approx_38_){
_start:
{
lean_inc(v_approx_38_);
return v_approx_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg___boxed(lean_object* v_approx_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg(v_approx_39_);
lean_dec(v_approx_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_approx_44_){
_start:
{
lean_inc(v_approx_44_);
return v_approx_44_;
}
}
LEAN_EXPORT void l_Lean_Util_ParamMinimizer_Status_approx_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_approx_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Util_ParamMinimizer_Status_approx_elim(lean_box(0), v_t_42_, lean_box(0), v_approx_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_approx_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_approx_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Util_ParamMinimizer_Status_approx_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_approx_49_);
lean_dec(v_approx_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg(lean_object* v_precise_52_){
_start:
{
lean_inc(v_precise_52_);
return v_precise_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg___boxed(lean_object* v_precise_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg(v_precise_53_);
lean_dec(v_precise_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_precise_58_){
_start:
{
lean_inc(v_precise_58_);
return v_precise_58_;
}
}
LEAN_EXPORT void l_Lean_Util_ParamMinimizer_Status_precise_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_precise_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Util_ParamMinimizer_Status_precise_elim(lean_box(0), v_t_56_, lean_box(0), v_precise_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_Status_precise_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_precise_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Util_ParamMinimizer_Status_precise_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_precise_63_);
lean_dec(v_precise_63_);
return v_res_65_;
}
}
static uint8_t _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus_default(void){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
static uint8_t _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(2u);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(1u);
v___x_80_ = lean_nat_to_int(v___x_79_);
return v___x_80_;
}
}
lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr(uint8_t v_x_81_, lean_object* v_prec_82_){
_start:
{
lean_object* v___y_84_; lean_object* v___y_91_; lean_object* v___y_98_; 
switch(v_x_81_)
{
case 0:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1024u);
v___x_105_ = lean_nat_dec_le(v___x_104_, v_prec_82_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6);
v___y_84_ = v___x_106_;
goto v___jp_83_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7);
v___y_84_ = v___x_107_;
goto v___jp_83_;
}
}
case 1:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(1024u);
v___x_109_ = lean_nat_dec_le(v___x_108_, v_prec_82_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6);
v___y_91_ = v___x_110_;
goto v___jp_90_;
}
else
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7);
v___y_91_ = v___x_111_;
goto v___jp_90_;
}
}
default: 
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(1024u);
v___x_113_ = lean_nat_dec_le(v___x_112_, v_prec_82_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6);
v___y_98_ = v___x_114_;
goto v___jp_97_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7, &l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once, _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7);
v___y_98_ = v___x_115_;
goto v___jp_97_;
}
}
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_85_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1));
lean_inc(v___y_84_);
v___x_86_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_86_, 0, v___y_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = 0;
v___x_88_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1, v___x_87_);
v___x_89_ = l_Repr_addAppParen(v___x_88_, v_prec_82_);
return v___x_89_;
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_92_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3));
lean_inc(v___y_91_);
v___x_93_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_93_, 0, v___y_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = 0;
v___x_95_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_94_);
v___x_96_ = l_Repr_addAppParen(v___x_95_, v_prec_82_);
return v___x_96_;
}
v___jp_97_:
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_99_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5));
lean_inc(v___y_98_);
v___x_100_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_100_, 0, v___y_98_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = 0;
v___x_102_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*1, v___x_101_);
v___x_103_ = l_Repr_addAppParen(v___x_102_, v_prec_82_);
return v___x_103_;
}
}
}
LEAN_EXPORT void l_Lean_Util_ParamMinimizer_instReprStatus_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_81_ = stack[0].m_num;
lean_object* v_prec_82_ = stack[1].m_obj;
lean_object* v_res_116_;
v_res_116_ = l_Lean_Util_ParamMinimizer_instReprStatus_repr(v_x_81_, v_prec_82_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_instReprStatus_repr___boxed(lean_object* v_x_117_, lean_object* v_prec_118_){
_start:
{
uint8_t v_x_171__boxed_119_; lean_object* v_res_120_; 
v_x_171__boxed_119_ = lean_unbox(v_x_117_);
v_res_120_ = l_Lean_Util_ParamMinimizer_instReprStatus_repr(v_x_171__boxed_119_, v_prec_118_);
lean_dec(v_prec_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0(lean_object* v_toPure_123_, lean_object* v_____x_124_){
_start:
{
lean_object* v_fst_125_; lean_object* v_snd_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_135_; 
v_fst_125_ = lean_ctor_get(v_____x_124_, 0);
v_snd_126_ = lean_ctor_get(v_____x_124_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_____x_124_);
if (v_isSharedCheck_135_ == 0)
{
v___x_128_ = v_____x_124_;
v_isShared_129_ = v_isSharedCheck_135_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_snd_126_);
lean_inc(v_fst_125_);
lean_dec(v_____x_124_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_135_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_130_, 0, v_fst_125_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_130_);
v___x_132_ = v___x_128_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_snd_126_);
v___x_132_ = v_reuseFailAlloc_134_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; 
v___x_133_ = lean_apply_2(v_toPure_123_, lean_box(0), v___x_132_);
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(lean_object* v_inst_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_toApplicative_138_; lean_object* v_toBind_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_162_; 
v_toApplicative_138_ = lean_ctor_get(v_inst_136_, 0);
v_toBind_139_ = lean_ctor_get(v_inst_136_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v_inst_136_);
if (v_isSharedCheck_162_ == 0)
{
v___x_141_ = v_inst_136_;
v_isShared_142_ = v_isSharedCheck_162_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_toBind_139_);
lean_inc(v_toApplicative_138_);
lean_dec(v_inst_136_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_162_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_toPure_143_; lean_object* v_cur_144_; lean_object* v_added_145_; lean_object* v_numCalls_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_161_; 
v_toPure_143_ = lean_ctor_get(v_toApplicative_138_, 1);
lean_inc(v_toPure_143_);
lean_dec_ref(v_toApplicative_138_);
v_cur_144_ = lean_ctor_get(v_a_137_, 0);
v_added_145_ = lean_ctor_get(v_a_137_, 1);
v_numCalls_146_ = lean_ctor_get(v_a_137_, 2);
v_isSharedCheck_161_ = !lean_is_exclusive(v_a_137_);
if (v_isSharedCheck_161_ == 0)
{
v___x_148_ = v_a_137_;
v_isShared_149_ = v_isSharedCheck_161_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_numCalls_146_);
lean_inc(v_added_145_);
lean_inc(v_cur_144_);
lean_dec(v_a_137_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_161_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___f_150_; lean_object* v___x_151_; uint8_t v___x_152_; lean_object* v___x_154_; 
lean_inc(v_toPure_143_);
v___f_150_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_150_, 0, v_toPure_143_);
v___x_151_ = lean_box(0);
v___x_152_ = 1;
if (v_isShared_149_ == 0)
{
v___x_154_ = v___x_148_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_cur_144_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_added_145_);
lean_ctor_set(v_reuseFailAlloc_160_, 2, v_numCalls_146_);
v___x_154_ = v_reuseFailAlloc_160_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_156_; 
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*3, v___x_152_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v___x_154_);
lean_ctor_set(v___x_141_, 0, v___x_151_);
v___x_156_ = v___x_141_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_154_);
v___x_156_ = v_reuseFailAlloc_159_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_apply_2(v_toPure_143_, lean_box(0), v___x_156_);
v___x_158_ = lean_apply_4(v_toBind_139_, lean_box(0), lean_box(0), v___x_157_, v___f_150_);
return v___x_158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound(lean_object* v_m_163_, lean_object* v_inst_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(v_inst_164_, v_a_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___boxed(lean_object* v_m_168_, lean_object* v_inst_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound(v_m_168_, v_inst_169_, v_a_170_, v_a_171_);
lean_dec_ref(v_a_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___redArg(lean_object* v_inst_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_toApplicative_175_; lean_object* v_toBind_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_201_; 
v_toApplicative_175_ = lean_ctor_get(v_inst_173_, 0);
v_toBind_176_ = lean_ctor_get(v_inst_173_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v_inst_173_);
if (v_isSharedCheck_201_ == 0)
{
v___x_178_ = v_inst_173_;
v_isShared_179_ = v_isSharedCheck_201_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_toBind_176_);
lean_inc(v_toApplicative_175_);
lean_dec(v_inst_173_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_201_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_toPure_180_; lean_object* v_cur_181_; lean_object* v_added_182_; lean_object* v_numCalls_183_; uint8_t v_found_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_200_; 
v_toPure_180_ = lean_ctor_get(v_toApplicative_175_, 1);
lean_inc(v_toPure_180_);
lean_dec_ref(v_toApplicative_175_);
v_cur_181_ = lean_ctor_get(v_a_174_, 0);
v_added_182_ = lean_ctor_get(v_a_174_, 1);
v_numCalls_183_ = lean_ctor_get(v_a_174_, 2);
v_found_184_ = lean_ctor_get_uint8(v_a_174_, sizeof(void*)*3);
v_isSharedCheck_200_ = !lean_is_exclusive(v_a_174_);
if (v_isSharedCheck_200_ == 0)
{
v___x_186_ = v_a_174_;
v_isShared_187_ = v_isSharedCheck_200_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_numCalls_183_);
lean_inc(v_added_182_);
lean_inc(v_cur_181_);
lean_dec(v_a_174_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_200_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
lean_inc(v_toPure_180_);
v___f_188_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_188_, 0, v_toPure_180_);
v___x_189_ = lean_box(0);
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_nat_add(v_numCalls_183_, v___x_190_);
lean_dec(v_numCalls_183_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 2, v___x_191_);
v___x_193_ = v___x_186_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_cur_181_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_added_182_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v___x_191_);
lean_ctor_set_uint8(v_reuseFailAlloc_199_, sizeof(void*)*3, v_found_184_);
v___x_193_ = v_reuseFailAlloc_199_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_193_);
lean_ctor_set(v___x_178_, 0, v___x_189_);
v___x_195_ = v___x_178_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_193_);
v___x_195_ = v_reuseFailAlloc_198_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_apply_2(v_toPure_180_, lean_box(0), v___x_195_);
v___x_197_ = lean_apply_4(v_toBind_176_, lean_box(0), lean_box(0), v___x_196_, v___f_188_);
return v___x_197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls(lean_object* v_m_202_, lean_object* v_inst_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___redArg(v_inst_203_, v_a_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___boxed(lean_object* v_m_207_, lean_object* v_inst_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls(v_m_207_, v_inst_208_, v_a_209_, v_a_210_);
lean_dec_ref(v_a_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(lean_object* v_i_212_, lean_object* v_inst_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_toApplicative_215_; lean_object* v_toBind_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_243_; 
v_toApplicative_215_ = lean_ctor_get(v_inst_213_, 0);
v_toBind_216_ = lean_ctor_get(v_inst_213_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v_inst_213_);
if (v_isSharedCheck_243_ == 0)
{
v___x_218_ = v_inst_213_;
v_isShared_219_ = v_isSharedCheck_243_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_toBind_216_);
lean_inc(v_toApplicative_215_);
lean_dec(v_inst_213_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_243_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v_toPure_220_; lean_object* v_cur_221_; lean_object* v_added_222_; lean_object* v_numCalls_223_; uint8_t v_found_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_242_; 
v_toPure_220_ = lean_ctor_get(v_toApplicative_215_, 1);
lean_inc(v_toPure_220_);
lean_dec_ref(v_toApplicative_215_);
v_cur_221_ = lean_ctor_get(v_a_214_, 0);
v_added_222_ = lean_ctor_get(v_a_214_, 1);
v_numCalls_223_ = lean_ctor_get(v_a_214_, 2);
v_found_224_ = lean_ctor_get_uint8(v_a_214_, sizeof(void*)*3);
v_isSharedCheck_242_ = !lean_is_exclusive(v_a_214_);
if (v_isSharedCheck_242_ == 0)
{
v___x_226_ = v_a_214_;
v_isShared_227_ = v_isSharedCheck_242_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_numCalls_223_);
lean_inc(v_added_222_);
lean_inc(v_cur_221_);
lean_dec(v_a_214_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_242_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___f_228_; lean_object* v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
lean_inc(v_toPure_220_);
v___f_228_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_228_, 0, v_toPure_220_);
v___x_229_ = lean_box(0);
v___x_230_ = 1;
v___x_231_ = lean_box(v___x_230_);
v___x_232_ = lean_array_set(v_cur_221_, v_i_212_, v___x_231_);
v___x_233_ = lean_array_push(v_added_222_, v_i_212_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_233_);
lean_ctor_set(v___x_226_, 0, v___x_232_);
v___x_235_ = v___x_226_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_numCalls_223_);
lean_ctor_set_uint8(v_reuseFailAlloc_241_, sizeof(void*)*3, v_found_224_);
v___x_235_ = v_reuseFailAlloc_241_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 1, v___x_235_);
lean_ctor_set(v___x_218_, 0, v___x_229_);
v___x_237_ = v___x_218_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_235_);
v___x_237_ = v_reuseFailAlloc_240_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_apply_2(v_toPure_220_, lean_box(0), v___x_237_);
v___x_239_ = lean_apply_4(v_toBind_216_, lean_box(0), lean_box(0), v___x_238_, v___f_228_);
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add(lean_object* v_m_244_, lean_object* v_i_245_, lean_object* v_inst_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(v_i_245_, v_inst_246_, v_a_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___boxed(lean_object* v_m_250_, lean_object* v_i_251_, lean_object* v_inst_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add(v_m_250_, v_i_251_, v_inst_252_, v_a_253_, v_a_254_);
lean_dec_ref(v_a_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(lean_object* v_i_256_, lean_object* v_inst_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_toApplicative_259_; lean_object* v_toBind_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_286_; 
v_toApplicative_259_ = lean_ctor_get(v_inst_257_, 0);
v_toBind_260_ = lean_ctor_get(v_inst_257_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v_inst_257_);
if (v_isSharedCheck_286_ == 0)
{
v___x_262_ = v_inst_257_;
v_isShared_263_ = v_isSharedCheck_286_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_toBind_260_);
lean_inc(v_toApplicative_259_);
lean_dec(v_inst_257_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_286_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_toPure_264_; lean_object* v_cur_265_; lean_object* v_added_266_; lean_object* v_numCalls_267_; uint8_t v_found_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_285_; 
v_toPure_264_ = lean_ctor_get(v_toApplicative_259_, 1);
lean_inc(v_toPure_264_);
lean_dec_ref(v_toApplicative_259_);
v_cur_265_ = lean_ctor_get(v_a_258_, 0);
v_added_266_ = lean_ctor_get(v_a_258_, 1);
v_numCalls_267_ = lean_ctor_get(v_a_258_, 2);
v_found_268_ = lean_ctor_get_uint8(v_a_258_, sizeof(void*)*3);
v_isSharedCheck_285_ = !lean_is_exclusive(v_a_258_);
if (v_isSharedCheck_285_ == 0)
{
v___x_270_ = v_a_258_;
v_isShared_271_ = v_isSharedCheck_285_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_numCalls_267_);
lean_inc(v_added_266_);
lean_inc(v_cur_265_);
lean_dec(v_a_258_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_285_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___f_272_; lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
lean_inc(v_toPure_264_);
v___f_272_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_272_, 0, v_toPure_264_);
v___x_273_ = lean_box(0);
v___x_274_ = 0;
v___x_275_ = lean_box(v___x_274_);
v___x_276_ = lean_array_set(v_cur_265_, v_i_256_, v___x_275_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_276_);
v___x_278_ = v___x_270_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_added_266_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_numCalls_267_);
lean_ctor_set_uint8(v_reuseFailAlloc_284_, sizeof(void*)*3, v_found_268_);
v___x_278_ = v_reuseFailAlloc_284_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_280_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_278_);
lean_ctor_set(v___x_262_, 0, v___x_273_);
v___x_280_ = v___x_262_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_278_);
v___x_280_ = v_reuseFailAlloc_283_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_apply_2(v_toPure_264_, lean_box(0), v___x_280_);
v___x_282_ = lean_apply_4(v_toBind_260_, lean_box(0), lean_box(0), v___x_281_, v___f_272_);
return v___x_282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg___boxed(lean_object* v_i_287_, lean_object* v_inst_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v_i_287_, v_inst_288_, v_a_289_);
lean_dec(v_i_287_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase(lean_object* v_m_291_, lean_object* v_i_292_, lean_object* v_inst_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v_i_292_, v_inst_293_, v_a_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___boxed(lean_object* v_m_297_, lean_object* v_i_298_, lean_object* v_inst_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase(v_m_297_, v_i_298_, v_inst_299_, v_a_300_, v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_i_298_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(lean_object* v_i_303_, lean_object* v_inst_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_toApplicative_306_; lean_object* v_toBind_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_333_; 
v_toApplicative_306_ = lean_ctor_get(v_inst_304_, 0);
v_toBind_307_ = lean_ctor_get(v_inst_304_, 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_inst_304_);
if (v_isSharedCheck_333_ == 0)
{
v___x_309_ = v_inst_304_;
v_isShared_310_ = v_isSharedCheck_333_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_toBind_307_);
lean_inc(v_toApplicative_306_);
lean_dec(v_inst_304_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_333_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v_toPure_311_; lean_object* v_cur_312_; lean_object* v_added_313_; lean_object* v_numCalls_314_; uint8_t v_found_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_332_; 
v_toPure_311_ = lean_ctor_get(v_toApplicative_306_, 1);
lean_inc(v_toPure_311_);
lean_dec_ref(v_toApplicative_306_);
v_cur_312_ = lean_ctor_get(v_a_305_, 0);
v_added_313_ = lean_ctor_get(v_a_305_, 1);
v_numCalls_314_ = lean_ctor_get(v_a_305_, 2);
v_found_315_ = lean_ctor_get_uint8(v_a_305_, sizeof(void*)*3);
v_isSharedCheck_332_ = !lean_is_exclusive(v_a_305_);
if (v_isSharedCheck_332_ == 0)
{
v___x_317_ = v_a_305_;
v_isShared_318_ = v_isSharedCheck_332_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_numCalls_314_);
lean_inc(v_added_313_);
lean_inc(v_cur_312_);
lean_dec(v_a_305_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_332_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___f_319_; lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
lean_inc(v_toPure_311_);
v___f_319_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_319_, 0, v_toPure_311_);
v___x_320_ = lean_box(0);
v___x_321_ = 1;
v___x_322_ = lean_box(v___x_321_);
v___x_323_ = lean_array_set(v_cur_312_, v_i_303_, v___x_322_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_323_);
v___x_325_ = v___x_317_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_added_313_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_numCalls_314_);
lean_ctor_set_uint8(v_reuseFailAlloc_331_, sizeof(void*)*3, v_found_315_);
v___x_325_ = v_reuseFailAlloc_331_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_327_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v___x_325_);
lean_ctor_set(v___x_309_, 0, v___x_320_);
v___x_327_ = v___x_309_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_330_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_apply_2(v_toPure_311_, lean_box(0), v___x_327_);
v___x_329_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v___x_328_, v___f_319_);
return v___x_329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg___boxed(lean_object* v_i_334_, lean_object* v_inst_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v_i_334_, v_inst_335_, v_a_336_);
lean_dec(v_i_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore(lean_object* v_m_338_, lean_object* v_i_339_, lean_object* v_inst_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v_i_339_, v_inst_340_, v_a_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___boxed(lean_object* v_m_344_, lean_object* v_i_345_, lean_object* v_inst_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore(v_m_344_, v_i_345_, v_inst_346_, v_a_347_, v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_i_345_);
return v_res_349_;
}
}
lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(lean_object* v_toPure_350_, uint8_t v___x_351_, lean_object* v_____x_352_){
_start:
{
lean_object* v_fst_353_; 
v_fst_353_ = lean_ctor_get(v_____x_352_, 0);
lean_inc(v_fst_353_);
if (lean_obj_tag(v_fst_353_) == 0)
{
lean_object* v_snd_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_370_; 
v_snd_354_ = lean_ctor_get(v_____x_352_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_____x_352_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v_____x_352_, 0);
lean_dec(v_unused_371_);
v___x_356_ = v_____x_352_;
v_isShared_357_ = v_isSharedCheck_370_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_snd_354_);
lean_dec(v_____x_352_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_370_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_369_; 
v_a_358_ = lean_ctor_get(v_fst_353_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v_fst_353_);
if (v_isSharedCheck_369_ == 0)
{
v___x_360_ = v_fst_353_;
v_isShared_361_ = v_isSharedCheck_369_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v_fst_353_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_369_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_368_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_363_);
v___x_365_ = v___x_356_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_snd_354_);
v___x_365_ = v_reuseFailAlloc_367_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = lean_apply_2(v_toPure_350_, lean_box(0), v___x_365_);
return v___x_366_;
}
}
}
}
}
else
{
lean_object* v_snd_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_389_; 
v_snd_372_ = lean_ctor_get(v_____x_352_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v_____x_352_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; 
v_unused_390_ = lean_ctor_get(v_____x_352_, 0);
lean_dec(v_unused_390_);
v___x_374_ = v_____x_352_;
v_isShared_375_ = v_isSharedCheck_389_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_snd_372_);
lean_dec(v_____x_352_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_389_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_387_; 
v_isSharedCheck_387_ = !lean_is_exclusive(v_fst_353_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v_fst_353_, 0);
lean_dec(v_unused_388_);
v___x_377_ = v_fst_353_;
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
else
{
lean_dec(v_fst_353_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = lean_box(v___x_351_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_386_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_383_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_381_);
v___x_383_ = v___x_374_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_snd_372_);
v___x_383_ = v_reuseFailAlloc_385_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; 
v___x_384_ = lean_apply_2(v_toPure_350_, lean_box(0), v___x_383_);
return v___x_384_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_350_ = stack[0].m_obj;
uint8_t v___x_351_ = stack[1].m_num;
lean_object* v_____x_352_ = stack[2].m_obj;
lean_object* v_res_391_;
v_res_391_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(v_toPure_350_, v___x_351_, v_____x_352_);
stack->m_obj
 = v_res_391_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed(lean_object* v_toPure_392_, lean_object* v___x_393_, lean_object* v_____x_394_){
_start:
{
uint8_t v___x_6887__boxed_395_; lean_object* v_res_396_; 
v___x_6887__boxed_395_ = lean_unbox(v___x_393_);
v_res_396_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(v_toPure_392_, v___x_6887__boxed_395_, v_____x_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1(lean_object* v_toPure_397_, lean_object* v_inst_398_, lean_object* v_toBind_399_, lean_object* v___f_400_, lean_object* v_____x_401_){
_start:
{
lean_object* v_fst_402_; 
v_fst_402_ = lean_ctor_get(v_____x_401_, 0);
if (lean_obj_tag(v_fst_402_) == 0)
{
lean_object* v___x_403_; 
lean_dec(v___f_400_);
lean_dec(v_toBind_399_);
lean_dec_ref(v_inst_398_);
v___x_403_ = lean_apply_2(v_toPure_397_, lean_box(0), v_____x_401_);
return v___x_403_;
}
else
{
lean_object* v_a_404_; uint8_t v___x_405_; 
v_a_404_ = lean_ctor_get(v_fst_402_, 0);
v___x_405_ = lean_unbox(v_a_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
lean_dec(v___f_400_);
lean_dec(v_toBind_399_);
lean_dec_ref(v_inst_398_);
v___x_406_ = lean_apply_2(v_toPure_397_, lean_box(0), v_____x_401_);
return v___x_406_;
}
else
{
lean_object* v_snd_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v_toPure_397_);
v_snd_407_ = lean_ctor_get(v_____x_401_, 1);
lean_inc(v_snd_407_);
lean_dec_ref(v_____x_401_);
v___x_408_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(v_inst_398_, v_snd_407_);
v___x_409_ = lean_apply_4(v_toBind_399_, lean_box(0), lean_box(0), v___x_408_, v___f_400_);
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__2(lean_object* v_toPure_410_, lean_object* v_____x_411_){
_start:
{
lean_object* v_fst_412_; lean_object* v_snd_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_422_; 
v_fst_412_ = lean_ctor_get(v_____x_411_, 0);
v_snd_413_ = lean_ctor_get(v_____x_411_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v_____x_411_);
if (v_isSharedCheck_422_ == 0)
{
v___x_415_ = v_____x_411_;
v_isShared_416_ = v_isSharedCheck_422_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_snd_413_);
lean_inc(v_fst_412_);
lean_dec(v_____x_411_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_422_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v_fst_412_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_snd_413_);
v___x_419_ = v_reuseFailAlloc_421_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_420_; 
v___x_420_ = lean_apply_2(v_toPure_410_, lean_box(0), v___x_419_);
return v___x_420_;
}
}
}
}
lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(lean_object* v_snd_423_, lean_object* v_toPure_424_, uint8_t v_a_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_box(v_a_425_);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v_snd_423_);
v___x_428_ = lean_apply_2(v_toPure_424_, lean_box(0), v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT void l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_423_ = stack[0].m_obj;
lean_object* v_toPure_424_ = stack[1].m_obj;
uint8_t v_a_425_ = stack[2].m_num;
lean_object* v_res_429_;
v_res_429_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(v_snd_423_, v_toPure_424_, v_a_425_);
stack->m_obj
 = v_res_429_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3___boxed(lean_object* v_snd_430_, lean_object* v_toPure_431_, lean_object* v_a_432_){
_start:
{
uint8_t v_a_boxed_433_; lean_object* v_res_434_; 
v_a_boxed_433_ = lean_unbox(v_a_432_);
v_res_434_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(v_snd_430_, v_toPure_431_, v_a_boxed_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4(lean_object* v_toPure_435_, lean_object* v_a_436_, lean_object* v_toBind_437_, lean_object* v___f_438_, lean_object* v_____x_439_){
_start:
{
lean_object* v_fst_440_; 
v_fst_440_ = lean_ctor_get(v_____x_439_, 0);
lean_inc(v_fst_440_);
if (lean_obj_tag(v_fst_440_) == 0)
{
lean_object* v_snd_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_457_; 
lean_dec(v___f_438_);
lean_dec(v_toBind_437_);
lean_dec_ref(v_a_436_);
v_snd_441_ = lean_ctor_get(v_____x_439_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v_____x_439_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v_____x_439_, 0);
lean_dec(v_unused_458_);
v___x_443_ = v_____x_439_;
v_isShared_444_ = v_isSharedCheck_457_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_snd_441_);
lean_dec(v_____x_439_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_457_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_456_; 
v_a_445_ = lean_ctor_get(v_fst_440_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v_fst_440_);
if (v_isSharedCheck_456_ == 0)
{
v___x_447_ = v_fst_440_;
v_isShared_448_ = v_isSharedCheck_456_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v_fst_440_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_456_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_455_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_450_);
v___x_452_ = v___x_443_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_snd_441_);
v___x_452_ = v_reuseFailAlloc_454_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; 
v___x_453_ = lean_apply_2(v_toPure_435_, lean_box(0), v___x_452_);
return v___x_453_;
}
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v_snd_460_; lean_object* v_test_461_; lean_object* v_cur_462_; lean_object* v___x_463_; lean_object* v___f_464_; lean_object* v___f_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_a_459_ = lean_ctor_get(v_fst_440_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v_fst_440_, 1);
v_snd_460_ = lean_ctor_get(v_____x_439_, 1);
lean_inc(v_snd_460_);
lean_dec_ref(v_____x_439_);
v_test_461_ = lean_ctor_get(v_a_436_, 1);
lean_inc(v_test_461_);
lean_dec_ref(v_a_436_);
v_cur_462_ = lean_ctor_get(v_a_459_, 0);
lean_inc_ref(v_cur_462_);
lean_dec(v_a_459_);
v___x_463_ = lean_apply_1(v_test_461_, v_cur_462_);
lean_inc(v_toPure_435_);
v___f_464_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__2), 2, 1);
lean_closure_set(v___f_464_, 0, v_toPure_435_);
v___f_465_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_465_, 0, v_snd_460_);
lean_closure_set(v___f_465_, 1, v_toPure_435_);
lean_inc_n(v_toBind_437_, 2);
v___x_466_ = lean_apply_4(v_toBind_437_, lean_box(0), lean_box(0), v___x_463_, v___f_465_);
v___x_467_ = lean_apply_4(v_toBind_437_, lean_box(0), lean_box(0), v___x_466_, v___f_464_);
v___x_468_ = lean_apply_4(v_toBind_437_, lean_box(0), lean_box(0), v___x_467_, v___f_438_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5(lean_object* v_toPure_469_, lean_object* v_____x_470_){
_start:
{
lean_object* v_fst_471_; lean_object* v_snd_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_481_; 
v_fst_471_ = lean_ctor_get(v_____x_470_, 0);
v_snd_472_ = lean_ctor_get(v_____x_470_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_____x_470_);
if (v_isSharedCheck_481_ == 0)
{
v___x_474_ = v_____x_470_;
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_snd_472_);
lean_inc(v_fst_471_);
lean_dec(v_____x_470_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v_fst_471_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_476_);
v___x_478_ = v___x_474_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_snd_472_);
v___x_478_ = v_reuseFailAlloc_480_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; 
v___x_479_ = lean_apply_2(v_toPure_469_, lean_box(0), v___x_478_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6(lean_object* v_toPure_482_, lean_object* v_toBind_483_, lean_object* v___f_484_, lean_object* v_____x_485_){
_start:
{
lean_object* v_fst_486_; 
v_fst_486_ = lean_ctor_get(v_____x_485_, 0);
lean_inc(v_fst_486_);
if (lean_obj_tag(v_fst_486_) == 0)
{
lean_object* v_snd_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_503_; 
lean_dec(v___f_484_);
lean_dec(v_toBind_483_);
v_snd_487_ = lean_ctor_get(v_____x_485_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v_____x_485_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v_____x_485_, 0);
lean_dec(v_unused_504_);
v___x_489_ = v_____x_485_;
v_isShared_490_ = v_isSharedCheck_503_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_snd_487_);
lean_dec(v_____x_485_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_503_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_502_; 
v_a_491_ = lean_ctor_get(v_fst_486_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_fst_486_);
if (v_isSharedCheck_502_ == 0)
{
v___x_493_ = v_fst_486_;
v_isShared_494_ = v_isSharedCheck_502_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v_fst_486_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_502_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_501_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_498_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_496_);
v___x_498_ = v___x_489_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_snd_487_);
v___x_498_ = v_reuseFailAlloc_500_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; 
v___x_499_ = lean_apply_2(v_toPure_482_, lean_box(0), v___x_498_);
return v___x_499_;
}
}
}
}
}
else
{
lean_object* v_snd_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_518_; 
v_snd_505_ = lean_ctor_get(v_____x_485_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_____x_485_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_____x_485_, 0);
lean_dec(v_unused_519_);
v___x_507_ = v_____x_485_;
v_isShared_508_ = v_isSharedCheck_518_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_snd_505_);
lean_dec(v_____x_485_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_518_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v_a_509_; lean_object* v___f_510_; lean_object* v___f_511_; lean_object* v___x_513_; 
v_a_509_ = lean_ctor_get(v_fst_486_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v_fst_486_, 1);
lean_inc(v_toBind_483_);
lean_inc_n(v_toPure_482_, 2);
v___f_510_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4), 5, 4);
lean_closure_set(v___f_510_, 0, v_toPure_482_);
lean_closure_set(v___f_510_, 1, v_a_509_);
lean_closure_set(v___f_510_, 2, v_toBind_483_);
lean_closure_set(v___f_510_, 3, v___f_484_);
v___f_511_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_511_, 0, v_toPure_482_);
lean_inc(v_snd_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v_snd_505_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_snd_505_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_snd_505_);
v___x_513_ = v_reuseFailAlloc_517_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_apply_2(v_toPure_482_, lean_box(0), v___x_513_);
lean_inc(v_toBind_483_);
v___x_515_ = lean_apply_4(v_toBind_483_, lean_box(0), lean_box(0), v___x_514_, v___f_511_);
v___x_516_ = lean_apply_4(v_toBind_483_, lean_box(0), lean_box(0), v___x_515_, v___f_510_);
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7(lean_object* v_toPure_520_, lean_object* v_a_521_, lean_object* v_toBind_522_, lean_object* v___f_523_, lean_object* v_____x_524_){
_start:
{
lean_object* v_fst_525_; 
v_fst_525_ = lean_ctor_get(v_____x_524_, 0);
lean_inc(v_fst_525_);
if (lean_obj_tag(v_fst_525_) == 0)
{
lean_object* v_snd_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_542_; 
lean_dec(v___f_523_);
lean_dec(v_toBind_522_);
v_snd_526_ = lean_ctor_get(v_____x_524_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_____x_524_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v_____x_524_, 0);
lean_dec(v_unused_543_);
v___x_528_ = v_____x_524_;
v_isShared_529_ = v_isSharedCheck_542_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_snd_526_);
lean_dec(v_____x_524_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_542_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_541_; 
v_a_530_ = lean_ctor_get(v_fst_525_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v_fst_525_);
if (v_isSharedCheck_541_ == 0)
{
v___x_532_ = v_fst_525_;
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v_fst_525_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_540_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_537_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_535_);
v___x_537_ = v___x_528_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_snd_526_);
v___x_537_ = v_reuseFailAlloc_539_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; 
v___x_538_ = lean_apply_2(v_toPure_520_, lean_box(0), v___x_537_);
return v___x_538_;
}
}
}
}
}
else
{
lean_object* v_snd_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_561_; 
v_snd_544_ = lean_ctor_get(v_____x_524_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v_____x_524_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; 
v_unused_562_ = lean_ctor_get(v_____x_524_, 0);
lean_dec(v_unused_562_);
v___x_546_ = v_____x_524_;
v_isShared_547_ = v_isSharedCheck_561_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_snd_544_);
lean_dec(v_____x_524_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_561_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_559_; 
v_isSharedCheck_559_ = !lean_is_exclusive(v_fst_525_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v_fst_525_, 0);
lean_dec(v_unused_560_);
v___x_549_ = v_fst_525_;
v_isShared_550_ = v_isSharedCheck_559_;
goto v_resetjp_548_;
}
else
{
lean_dec(v_fst_525_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_559_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
lean_inc_ref(v_a_521_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v_a_521_);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_521_);
v___x_552_ = v_reuseFailAlloc_558_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_554_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_552_);
v___x_554_ = v___x_546_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_snd_544_);
v___x_554_ = v_reuseFailAlloc_557_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_apply_2(v_toPure_520_, lean_box(0), v___x_554_);
v___x_556_ = lean_apply_4(v_toBind_522_, lean_box(0), lean_box(0), v___x_555_, v___f_523_);
return v___x_556_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7___boxed(lean_object* v_toPure_563_, lean_object* v_a_564_, lean_object* v_toBind_565_, lean_object* v___f_566_, lean_object* v_____x_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7(v_toPure_563_, v_a_564_, v_toBind_565_, v___f_566_, v_____x_567_);
lean_dec_ref(v_a_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(lean_object* v_toPure_571_, lean_object* v_inst_572_, lean_object* v_toBind_573_, lean_object* v_a_574_, lean_object* v_maxCalls_575_, lean_object* v_____x_576_){
_start:
{
lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_628_; 
v_fst_577_ = lean_ctor_get(v_____x_576_, 0);
v_snd_578_ = lean_ctor_get(v_____x_576_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_____x_576_);
if (v_isSharedCheck_628_ == 0)
{
v___x_580_ = v_____x_576_;
v_isShared_581_ = v_isSharedCheck_628_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_snd_578_);
lean_inc(v_fst_577_);
lean_dec(v_____x_576_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_628_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
if (lean_obj_tag(v_fst_577_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_619_; 
lean_del_object(v___x_580_);
lean_dec(v_toBind_573_);
lean_dec_ref(v_inst_572_);
v_a_610_ = lean_ctor_get(v_fst_577_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v_fst_577_);
if (v_isSharedCheck_619_ == 0)
{
v___x_612_ = v_fst_577_;
v_isShared_613_ = v_isSharedCheck_619_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v_fst_577_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_619_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_618_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v_snd_578_);
v___x_617_ = lean_apply_2(v_toPure_571_, lean_box(0), v___x_616_);
return v___x_617_;
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v_a_620_ = lean_ctor_get(v_fst_577_, 0);
lean_inc(v_a_620_);
lean_dec_ref_known(v_fst_577_, 1);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_nat_dec_lt(v___x_621_, v_maxCalls_575_);
if (v___x_622_ == 0)
{
lean_dec(v_a_620_);
goto v___jp_582_;
}
else
{
lean_object* v_numCalls_623_; uint8_t v___x_624_; 
v_numCalls_623_ = lean_ctor_get(v_a_620_, 2);
lean_inc(v_numCalls_623_);
lean_dec(v_a_620_);
v___x_624_ = lean_nat_dec_le(v_maxCalls_575_, v_numCalls_623_);
lean_dec(v_numCalls_623_);
if (v___x_624_ == 0)
{
goto v___jp_582_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_del_object(v___x_580_);
lean_dec(v_toBind_573_);
lean_dec_ref(v_inst_572_);
v___x_625_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0));
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v_snd_578_);
v___x_627_ = lean_apply_2(v_toPure_571_, lean_box(0), v___x_626_);
return v___x_627_;
}
}
}
v___jp_582_:
{
lean_object* v_cur_583_; lean_object* v_added_584_; lean_object* v_numCalls_585_; uint8_t v_found_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_609_; 
v_cur_583_ = lean_ctor_get(v_snd_578_, 0);
v_added_584_ = lean_ctor_get(v_snd_578_, 1);
v_numCalls_585_ = lean_ctor_get(v_snd_578_, 2);
v_found_586_ = lean_ctor_get_uint8(v_snd_578_, sizeof(void*)*3);
v_isSharedCheck_609_ = !lean_is_exclusive(v_snd_578_);
if (v_isSharedCheck_609_ == 0)
{
v___x_588_ = v_snd_578_;
v_isShared_589_ = v_isSharedCheck_609_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_numCalls_585_);
lean_inc(v_added_584_);
lean_inc(v_cur_583_);
lean_dec(v_snd_578_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_609_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
uint8_t v___x_590_; lean_object* v___x_591_; lean_object* v___f_592_; lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_590_ = 1;
v___x_591_ = lean_box(v___x_590_);
lean_inc_n(v_toPure_571_, 5);
v___f_592_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_592_, 0, v_toPure_571_);
lean_closure_set(v___f_592_, 1, v___x_591_);
lean_inc_n(v_toBind_573_, 3);
v___f_593_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1), 5, 4);
lean_closure_set(v___f_593_, 0, v_toPure_571_);
lean_closure_set(v___f_593_, 1, v_inst_572_);
lean_closure_set(v___f_593_, 2, v_toBind_573_);
lean_closure_set(v___f_593_, 3, v___f_592_);
v___f_594_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6), 4, 3);
lean_closure_set(v___f_594_, 0, v_toPure_571_);
lean_closure_set(v___f_594_, 1, v_toBind_573_);
lean_closure_set(v___f_594_, 2, v___f_593_);
lean_inc_ref(v_a_574_);
v___f_595_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7___boxed), 5, 4);
lean_closure_set(v___f_595_, 0, v_toPure_571_);
lean_closure_set(v___f_595_, 1, v_a_574_);
lean_closure_set(v___f_595_, 2, v_toBind_573_);
lean_closure_set(v___f_595_, 3, v___f_594_);
v___f_596_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0), 2, 1);
lean_closure_set(v___f_596_, 0, v_toPure_571_);
v___x_597_ = lean_box(0);
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_add(v_numCalls_585_, v___x_598_);
lean_dec(v_numCalls_585_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 2, v___x_599_);
v___x_601_ = v___x_588_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_cur_583_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_added_584_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v___x_599_);
lean_ctor_set_uint8(v_reuseFailAlloc_608_, sizeof(void*)*3, v_found_586_);
v___x_601_ = v_reuseFailAlloc_608_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_603_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_601_);
lean_ctor_set(v___x_580_, 0, v___x_597_);
v___x_603_ = v___x_580_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v___x_601_);
v___x_603_ = v_reuseFailAlloc_607_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_apply_2(v_toPure_571_, lean_box(0), v___x_603_);
lean_inc(v_toBind_573_);
v___x_605_ = lean_apply_4(v_toBind_573_, lean_box(0), lean_box(0), v___x_604_, v___f_596_);
v___x_606_ = lean_apply_4(v_toBind_573_, lean_box(0), lean_box(0), v___x_605_, v___f_595_);
return v___x_606_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed(lean_object* v_toPure_629_, lean_object* v_inst_630_, lean_object* v_toBind_631_, lean_object* v_a_632_, lean_object* v_maxCalls_633_, lean_object* v_____x_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(v_toPure_629_, v_inst_630_, v_toBind_631_, v_a_632_, v_maxCalls_633_, v_____x_634_);
lean_dec(v_maxCalls_633_);
lean_dec_ref(v_a_632_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(lean_object* v_toPure_636_, lean_object* v_inst_637_, lean_object* v_toBind_638_, lean_object* v_a_639_, lean_object* v_____x_640_){
_start:
{
lean_object* v_fst_641_; 
v_fst_641_ = lean_ctor_get(v_____x_640_, 0);
lean_inc(v_fst_641_);
if (lean_obj_tag(v_fst_641_) == 0)
{
lean_object* v_snd_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_658_; 
lean_dec(v_toBind_638_);
lean_dec_ref(v_inst_637_);
v_snd_642_ = lean_ctor_get(v_____x_640_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_____x_640_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; 
v_unused_659_ = lean_ctor_get(v_____x_640_, 0);
lean_dec(v_unused_659_);
v___x_644_ = v_____x_640_;
v_isShared_645_ = v_isSharedCheck_658_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_snd_642_);
lean_dec(v_____x_640_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_658_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_657_; 
v_a_646_ = lean_ctor_get(v_fst_641_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_fst_641_);
if (v_isSharedCheck_657_ == 0)
{
v___x_648_ = v_fst_641_;
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v_fst_641_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_656_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_651_);
v___x_653_ = v___x_644_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_snd_642_);
v___x_653_ = v_reuseFailAlloc_655_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; 
v___x_654_ = lean_apply_2(v_toPure_636_, lean_box(0), v___x_653_);
return v___x_654_;
}
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v_snd_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_674_; 
v_a_660_ = lean_ctor_get(v_fst_641_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v_fst_641_, 1);
v_snd_661_ = lean_ctor_get(v_____x_640_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_____x_640_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v_____x_640_, 0);
lean_dec(v_unused_675_);
v___x_663_ = v_____x_640_;
v_isShared_664_ = v_isSharedCheck_674_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_snd_661_);
lean_dec(v_____x_640_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_674_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_maxCalls_665_; lean_object* v___f_666_; lean_object* v___f_667_; lean_object* v___x_669_; 
v_maxCalls_665_ = lean_ctor_get(v_a_660_, 2);
lean_inc(v_maxCalls_665_);
lean_dec(v_a_660_);
lean_inc_ref(v_a_639_);
lean_inc(v_toBind_638_);
lean_inc_n(v_toPure_636_, 2);
v___f_666_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_666_, 0, v_toPure_636_);
lean_closure_set(v___f_666_, 1, v_inst_637_);
lean_closure_set(v___f_666_, 2, v_toBind_638_);
lean_closure_set(v___f_666_, 3, v_a_639_);
lean_closure_set(v___f_666_, 4, v_maxCalls_665_);
v___f_667_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_667_, 0, v_toPure_636_);
lean_inc(v_snd_661_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v_snd_661_);
v___x_669_ = v___x_663_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_snd_661_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_snd_661_);
v___x_669_ = v_reuseFailAlloc_673_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = lean_apply_2(v_toPure_636_, lean_box(0), v___x_669_);
lean_inc(v_toBind_638_);
v___x_671_ = lean_apply_4(v_toBind_638_, lean_box(0), lean_box(0), v___x_670_, v___f_667_);
v___x_672_ = lean_apply_4(v_toBind_638_, lean_box(0), lean_box(0), v___x_671_, v___f_666_);
return v___x_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed(lean_object* v_toPure_676_, lean_object* v_inst_677_, lean_object* v_toBind_678_, lean_object* v_a_679_, lean_object* v_____x_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(v_toPure_676_, v_inst_677_, v_toBind_678_, v_a_679_, v_____x_680_);
lean_dec_ref(v_a_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(lean_object* v_inst_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_toApplicative_685_; lean_object* v_toBind_686_; lean_object* v_toPure_687_; lean_object* v___f_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_toApplicative_685_ = lean_ctor_get(v_inst_682_, 0);
v_toBind_686_ = lean_ctor_get(v_inst_682_, 1);
lean_inc_n(v_toBind_686_, 2);
v_toPure_687_ = lean_ctor_get(v_toApplicative_685_, 1);
lean_inc_n(v_toPure_687_, 2);
lean_inc_ref_n(v_a_683_, 2);
v___f_688_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed), 5, 4);
lean_closure_set(v___f_688_, 0, v_toPure_687_);
lean_closure_set(v___f_688_, 1, v_inst_682_);
lean_closure_set(v___f_688_, 2, v_toBind_686_);
lean_closure_set(v___f_688_, 3, v_a_683_);
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v_a_683_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_a_684_);
v___x_691_ = lean_apply_2(v_toPure_687_, lean_box(0), v___x_690_);
v___x_692_ = lean_apply_4(v_toBind_686_, lean_box(0), lean_box(0), v___x_691_, v___f_688_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___boxed(lean_object* v_inst_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_693_, v_a_694_, v_a_695_);
lean_dec_ref(v_a_694_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(lean_object* v_m_697_, lean_object* v_inst_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_698_, v_a_699_, v_a_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___boxed(lean_object* v_m_702_, lean_object* v_inst_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(v_m_702_, v_inst_703_, v_a_704_, v_a_705_);
lean_dec_ref(v_a_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0(lean_object* v_toPure_707_, lean_object* v_____x_708_){
_start:
{
lean_object* v_fst_709_; 
v_fst_709_ = lean_ctor_get(v_____x_708_, 0);
lean_inc(v_fst_709_);
if (lean_obj_tag(v_fst_709_) == 0)
{
lean_object* v_snd_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_726_; 
v_snd_710_ = lean_ctor_get(v_____x_708_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_____x_708_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v_____x_708_, 0);
lean_dec(v_unused_727_);
v___x_712_ = v_____x_708_;
v_isShared_713_ = v_isSharedCheck_726_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snd_710_);
lean_dec(v_____x_708_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_726_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_725_; 
v_a_714_ = lean_ctor_get(v_fst_709_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v_fst_709_);
if (v_isSharedCheck_725_ == 0)
{
v___x_716_ = v_fst_709_;
v_isShared_717_ = v_isSharedCheck_725_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v_fst_709_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_725_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_724_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_719_);
v___x_721_ = v___x_712_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_snd_710_);
v___x_721_ = v_reuseFailAlloc_723_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; 
v___x_722_ = lean_apply_2(v_toPure_707_, lean_box(0), v___x_721_);
return v___x_722_;
}
}
}
}
}
else
{
lean_object* v_snd_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_744_; 
v_snd_728_ = lean_ctor_get(v_____x_708_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_____x_708_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_____x_708_, 0);
lean_dec(v_unused_745_);
v___x_730_ = v_____x_708_;
v_isShared_731_ = v_isSharedCheck_744_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_snd_728_);
lean_dec(v_____x_708_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_744_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_743_; 
v_a_732_ = lean_ctor_get(v_fst_709_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v_fst_709_);
if (v_isSharedCheck_743_ == 0)
{
v___x_734_ = v_fst_709_;
v_isShared_735_ = v_isSharedCheck_743_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v_fst_709_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_743_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_742_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_739_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_737_);
v___x_739_ = v___x_730_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_snd_728_);
v___x_739_ = v_reuseFailAlloc_741_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_740_; 
v___x_740_ = lean_apply_2(v_toPure_707_, lean_box(0), v___x_739_);
return v___x_740_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1(lean_object* v_toPure_746_, lean_object* v___x_747_, lean_object* v_____x_748_){
_start:
{
lean_object* v_fst_749_; 
v_fst_749_ = lean_ctor_get(v_____x_748_, 0);
lean_inc(v_fst_749_);
if (lean_obj_tag(v_fst_749_) == 0)
{
lean_object* v_snd_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_766_; 
v_snd_750_ = lean_ctor_get(v_____x_748_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v_____x_748_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; 
v_unused_767_ = lean_ctor_get(v_____x_748_, 0);
lean_dec(v_unused_767_);
v___x_752_ = v_____x_748_;
v_isShared_753_ = v_isSharedCheck_766_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_snd_750_);
lean_dec(v_____x_748_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_766_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_765_; 
v_a_754_ = lean_ctor_get(v_fst_749_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v_fst_749_);
if (v_isSharedCheck_765_ == 0)
{
v___x_756_ = v_fst_749_;
v_isShared_757_ = v_isSharedCheck_765_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v_fst_749_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_765_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_764_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_761_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_759_);
v___x_761_ = v___x_752_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_snd_750_);
v___x_761_ = v_reuseFailAlloc_763_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; 
v___x_762_ = lean_apply_2(v_toPure_746_, lean_box(0), v___x_761_);
return v___x_762_;
}
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_795_; 
v_a_768_ = lean_ctor_get(v_fst_749_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_fst_749_);
if (v_isSharedCheck_795_ == 0)
{
v___x_770_ = v_fst_749_;
v_isShared_771_ = v_isSharedCheck_795_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v_fst_749_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_795_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v_fst_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_793_; 
v_fst_772_ = lean_ctor_get(v_a_768_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v_a_768_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_a_768_, 1);
lean_dec(v_unused_794_);
v___x_774_ = v_a_768_;
v_isShared_775_ = v_isSharedCheck_793_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_fst_772_);
lean_dec(v_a_768_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_793_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
if (lean_obj_tag(v_fst_772_) == 0)
{
lean_object* v_snd_776_; lean_object* v___x_778_; 
v_snd_776_ = lean_ctor_get(v_____x_748_, 1);
lean_inc(v_snd_776_);
lean_dec_ref(v_____x_748_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_747_);
v___x_778_ = v___x_770_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_747_);
v___x_778_ = v_reuseFailAlloc_783_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v_snd_776_);
lean_ctor_set(v___x_774_, 0, v___x_778_);
v___x_780_ = v___x_774_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_snd_776_);
v___x_780_ = v_reuseFailAlloc_782_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; 
v___x_781_ = lean_apply_2(v_toPure_746_, lean_box(0), v___x_780_);
return v___x_781_;
}
}
}
else
{
lean_object* v_snd_784_; lean_object* v_val_785_; lean_object* v___x_787_; 
v_snd_784_ = lean_ctor_get(v_____x_748_, 1);
lean_inc(v_snd_784_);
lean_dec_ref(v_____x_748_);
v_val_785_ = lean_ctor_get(v_fst_772_, 0);
lean_inc(v_val_785_);
lean_dec_ref_known(v_fst_772_, 1);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v_val_785_);
v___x_787_ = v___x_770_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_val_785_);
v___x_787_ = v_reuseFailAlloc_792_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_789_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v_snd_784_);
lean_ctor_set(v___x_774_, 0, v___x_787_);
v___x_789_ = v___x_774_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_snd_784_);
v___x_789_ = v_reuseFailAlloc_791_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; 
v___x_790_ = lean_apply_2(v_toPure_746_, lean_box(0), v___x_789_);
return v___x_790_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2(lean_object* v_toPure_796_, lean_object* v___x_797_, lean_object* v___x_798_, lean_object* v_____x_799_){
_start:
{
lean_object* v_fst_800_; 
v_fst_800_ = lean_ctor_get(v_____x_799_, 0);
lean_inc(v_fst_800_);
if (lean_obj_tag(v_fst_800_) == 0)
{
lean_object* v_snd_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v___x_797_);
v_snd_801_ = lean_ctor_get(v_____x_799_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_____x_799_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_____x_799_, 0);
lean_dec(v_unused_818_);
v___x_803_ = v_____x_799_;
v_isShared_804_ = v_isSharedCheck_817_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_snd_801_);
lean_dec(v_____x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_817_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_816_; 
v_a_805_ = lean_ctor_get(v_fst_800_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v_fst_800_);
if (v_isSharedCheck_816_ == 0)
{
v___x_807_ = v_fst_800_;
v_isShared_808_ = v_isSharedCheck_816_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v_fst_800_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_816_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_815_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_812_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_810_);
v___x_812_ = v___x_803_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_snd_801_);
v___x_812_ = v_reuseFailAlloc_814_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; 
v___x_813_ = lean_apply_2(v_toPure_796_, lean_box(0), v___x_812_);
return v___x_813_;
}
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_854_; 
v_a_819_ = lean_ctor_get(v_fst_800_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v_fst_800_);
if (v_isSharedCheck_854_ == 0)
{
v___x_821_ = v_fst_800_;
v_isShared_822_ = v_isSharedCheck_854_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v_fst_800_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_854_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint8_t v___x_823_; 
v___x_823_ = lean_unbox(v_a_819_);
lean_dec(v_a_819_);
if (v___x_823_ == 0)
{
lean_object* v_snd_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_836_; 
v_snd_824_ = lean_ctor_get(v_____x_799_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_____x_799_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v_____x_799_, 0);
lean_dec(v_unused_837_);
v___x_826_ = v_____x_799_;
v_isShared_827_ = v_isSharedCheck_836_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_snd_824_);
lean_dec(v_____x_799_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_836_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_797_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_828_);
v___x_830_ = v___x_821_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_835_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_832_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_830_);
v___x_832_ = v___x_826_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_snd_824_);
v___x_832_ = v_reuseFailAlloc_834_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; 
v___x_833_ = lean_apply_2(v_toPure_796_, lean_box(0), v___x_832_);
return v___x_833_;
}
}
}
}
else
{
lean_object* v_snd_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_852_; 
lean_dec_ref(v___x_797_);
v_snd_838_ = lean_ctor_get(v_____x_799_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_____x_799_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_____x_799_, 0);
lean_dec(v_unused_853_);
v___x_840_ = v_____x_799_;
v_isShared_841_ = v_isSharedCheck_852_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_snd_838_);
lean_dec(v_____x_799_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_852_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_798_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_798_);
lean_ctor_set(v___x_840_, 0, v___x_842_);
v___x_844_ = v___x_840_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v___x_798_);
v___x_844_ = v_reuseFailAlloc_851_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_845_);
v___x_847_ = v___x_821_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_850_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v_snd_838_);
v___x_849_ = lean_apply_2(v_toPure_796_, lean_box(0), v___x_848_);
return v___x_849_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(lean_object* v_inst_855_, lean_object* v_toBind_856_, lean_object* v___f_857_, lean_object* v_____r_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_855_, v___y_859_, v___y_860_);
v___x_862_ = lean_apply_4(v_toBind_856_, lean_box(0), lean_box(0), v___x_861_, v___f_857_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed(lean_object* v_inst_863_, lean_object* v_toBind_864_, lean_object* v___f_865_, lean_object* v_____r_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(v_inst_863_, v_toBind_864_, v___f_865_, v_____r_866_, v___y_867_, v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(lean_object* v_toPure_870_, lean_object* v_next_871_, lean_object* v_G_872_, lean_object* v___y_873_, lean_object* v_____x_874_){
_start:
{
lean_object* v_fst_875_; 
v_fst_875_ = lean_ctor_get(v_____x_874_, 0);
lean_inc(v_fst_875_);
if (lean_obj_tag(v_fst_875_) == 0)
{
lean_object* v_snd_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_G_872_);
v_snd_876_ = lean_ctor_get(v_____x_874_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v_____x_874_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_____x_874_, 0);
lean_dec(v_unused_893_);
v___x_878_ = v_____x_874_;
v_isShared_879_ = v_isSharedCheck_892_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_snd_876_);
lean_dec(v_____x_874_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_892_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_891_; 
v_a_880_ = lean_ctor_get(v_fst_875_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v_fst_875_);
if (v_isSharedCheck_891_ == 0)
{
v___x_882_ = v_fst_875_;
v_isShared_883_ = v_isSharedCheck_891_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v_fst_875_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_891_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_890_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_885_);
v___x_887_ = v___x_878_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_snd_876_);
v___x_887_ = v_reuseFailAlloc_889_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; 
v___x_888_ = lean_apply_2(v_toPure_870_, lean_box(0), v___x_887_);
return v___x_888_;
}
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_917_; 
v_a_894_ = lean_ctor_get(v_fst_875_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_fst_875_);
if (v_isSharedCheck_917_ == 0)
{
v___x_896_ = v_fst_875_;
v_isShared_897_ = v_isSharedCheck_917_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v_fst_875_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_917_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
if (lean_obj_tag(v_a_894_) == 0)
{
lean_object* v_snd_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_G_872_);
v_snd_898_ = lean_ctor_get(v_____x_874_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v_____x_874_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v_____x_874_, 0);
lean_dec(v_unused_911_);
v___x_900_ = v_____x_874_;
v_isShared_901_ = v_isSharedCheck_910_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_snd_898_);
lean_dec(v_____x_874_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_910_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v_a_902_; lean_object* v___x_904_; 
v_a_902_ = lean_ctor_get(v_a_894_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v_a_894_, 1);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v_a_902_);
v___x_904_ = v___x_896_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_902_);
v___x_904_ = v_reuseFailAlloc_909_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_906_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_904_);
v___x_906_ = v___x_900_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_snd_898_);
v___x_906_ = v_reuseFailAlloc_908_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; 
v___x_907_ = lean_apply_2(v_toPure_870_, lean_box(0), v___x_906_);
return v___x_907_;
}
}
}
}
else
{
lean_object* v_snd_912_; lean_object* v_a_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
lean_del_object(v___x_896_);
lean_dec(v_toPure_870_);
v_snd_912_ = lean_ctor_get(v_____x_874_, 1);
lean_inc(v_snd_912_);
lean_dec_ref(v_____x_874_);
v_a_913_ = lean_ctor_get(v_a_894_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v_a_894_, 1);
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_nat_add(v_next_871_, v___x_914_);
lean_inc_ref(v___y_873_);
v___x_916_ = lean_apply_6(v_G_872_, v___x_915_, v_a_913_, lean_box(0), lean_box(0), v___y_873_, v_snd_912_);
return v___x_916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed(lean_object* v_toPure_918_, lean_object* v_next_919_, lean_object* v_G_920_, lean_object* v___y_921_, lean_object* v_____x_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(v_toPure_918_, v_next_919_, v_G_920_, v___y_921_, v_____x_922_);
lean_dec_ref(v___y_921_);
lean_dec(v_next_919_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(lean_object* v_toPure_924_, lean_object* v___f_925_, lean_object* v___y_926_, lean_object* v_____x_927_){
_start:
{
lean_object* v_fst_928_; 
v_fst_928_ = lean_ctor_get(v_____x_927_, 0);
lean_inc(v_fst_928_);
if (lean_obj_tag(v_fst_928_) == 0)
{
lean_object* v_snd_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_945_; 
lean_dec(v___f_925_);
v_snd_929_ = lean_ctor_get(v_____x_927_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v_____x_927_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v_____x_927_, 0);
lean_dec(v_unused_946_);
v___x_931_ = v_____x_927_;
v_isShared_932_ = v_isSharedCheck_945_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_snd_929_);
lean_dec(v_____x_927_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_945_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_944_; 
v_a_933_ = lean_ctor_get(v_fst_928_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v_fst_928_);
if (v_isSharedCheck_944_ == 0)
{
v___x_935_ = v_fst_928_;
v_isShared_936_ = v_isSharedCheck_944_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v_fst_928_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_944_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_943_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_938_);
v___x_940_ = v___x_931_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_snd_929_);
v___x_940_ = v_reuseFailAlloc_942_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; 
v___x_941_ = lean_apply_2(v_toPure_924_, lean_box(0), v___x_940_);
return v___x_941_;
}
}
}
}
}
else
{
lean_object* v_snd_947_; lean_object* v_a_948_; lean_object* v___x_949_; 
lean_dec(v_toPure_924_);
v_snd_947_ = lean_ctor_get(v_____x_927_, 1);
lean_inc(v_snd_947_);
lean_dec_ref(v_____x_927_);
v_a_948_ = lean_ctor_get(v_fst_928_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v_fst_928_, 1);
lean_inc_ref(v___y_926_);
v___x_949_ = lean_apply_3(v___f_925_, v_a_948_, v___y_926_, v_snd_947_);
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed(lean_object* v_toPure_950_, lean_object* v___f_951_, lean_object* v___y_952_, lean_object* v_____x_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(v_toPure_950_, v___f_951_, v___y_952_, v_____x_953_);
lean_dec_ref(v___y_952_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(lean_object* v___x_955_, lean_object* v_toPure_956_, lean_object* v_toBind_957_, lean_object* v___f_958_, lean_object* v_initialMask_959_, lean_object* v___f_960_, lean_object* v_inst_961_, lean_object* v___x_962_, lean_object* v_next_963_, lean_object* v_acc_964_, lean_object* v_h_965_, lean_object* v_G_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
uint8_t v___x_969_; 
v___x_969_ = lean_nat_dec_lt(v_next_963_, v___x_955_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec(v_G_966_);
lean_dec(v_next_963_);
lean_dec_ref(v_inst_961_);
lean_dec(v___f_960_);
lean_dec(v___f_958_);
lean_dec(v_toBind_957_);
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v_acc_964_);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v___y_968_);
v___x_972_ = lean_apply_2(v_toPure_956_, lean_box(0), v___x_971_);
return v___x_972_;
}
else
{
lean_object* v___f_973_; lean_object* v___y_975_; lean_object* v___x_978_; uint8_t v___x_979_; 
lean_dec_ref(v_acc_964_);
lean_inc_ref(v___y_967_);
lean_inc(v_next_963_);
lean_inc(v_toPure_956_);
v___f_973_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_973_, 0, v_toPure_956_);
lean_closure_set(v___f_973_, 1, v_next_963_);
lean_closure_set(v___f_973_, 2, v_G_966_);
lean_closure_set(v___f_973_, 3, v___y_967_);
v___x_978_ = lean_array_fget_borrowed(v_initialMask_959_, v_next_963_);
v___x_979_ = lean_unbox(v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___f_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
lean_inc_ref(v___y_967_);
v___f_980_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_980_, 0, v_toPure_956_);
lean_closure_set(v___f_980_, 1, v___f_960_);
lean_closure_set(v___f_980_, 2, v___y_967_);
v___x_981_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(v_next_963_, v_inst_961_, v___y_968_);
lean_inc(v_toBind_957_);
v___x_982_ = lean_apply_4(v_toBind_957_, lean_box(0), lean_box(0), v___x_981_, v___f_980_);
v___y_975_ = v___x_982_;
goto v___jp_974_;
}
else
{
lean_object* v___x_983_; 
lean_dec(v_next_963_);
lean_dec_ref(v_inst_961_);
lean_dec(v_toPure_956_);
lean_inc_ref(v___y_967_);
v___x_983_ = lean_apply_3(v___f_960_, v___x_962_, v___y_967_, v___y_968_);
v___y_975_ = v___x_983_;
goto v___jp_974_;
}
v___jp_974_:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
lean_inc(v_toBind_957_);
v___x_976_ = lean_apply_4(v_toBind_957_, lean_box(0), lean_box(0), v___y_975_, v___f_958_);
v___x_977_ = lean_apply_4(v_toBind_957_, lean_box(0), lean_box(0), v___x_976_, v___f_973_);
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed(lean_object* v___x_984_, lean_object* v_toPure_985_, lean_object* v_toBind_986_, lean_object* v___f_987_, lean_object* v_initialMask_988_, lean_object* v___f_989_, lean_object* v_inst_990_, lean_object* v___x_991_, lean_object* v_next_992_, lean_object* v_acc_993_, lean_object* v_h_994_, lean_object* v_G_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(v___x_984_, v_toPure_985_, v_toBind_986_, v___f_987_, v_initialMask_988_, v___f_989_, v_inst_990_, v___x_991_, v_next_992_, v_acc_993_, v_h_994_, v_G_995_, v___y_996_, v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec_ref(v_initialMask_988_);
lean_dec(v___x_984_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(lean_object* v_toPure_1002_, lean_object* v_inst_1003_, lean_object* v_toBind_1004_, lean_object* v___f_1005_, lean_object* v_a_1006_, lean_object* v_____x_1007_){
_start:
{
lean_object* v_fst_1008_; 
v_fst_1008_ = lean_ctor_get(v_____x_1007_, 0);
lean_inc(v_fst_1008_);
if (lean_obj_tag(v_fst_1008_) == 0)
{
lean_object* v_snd_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v___f_1005_);
lean_dec(v_toBind_1004_);
lean_dec_ref(v_inst_1003_);
v_snd_1009_ = lean_ctor_get(v_____x_1007_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_____x_1007_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v_____x_1007_, 0);
lean_dec(v_unused_1026_);
v___x_1011_ = v_____x_1007_;
v_isShared_1012_ = v_isSharedCheck_1025_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_snd_1009_);
lean_dec(v_____x_1007_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1025_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1024_; 
v_a_1013_ = lean_ctor_get(v_fst_1008_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_fst_1008_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1015_ = v_fst_1008_;
v_isShared_1016_ = v_isSharedCheck_1024_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v_fst_1008_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1024_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1020_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1018_);
v___x_1020_ = v___x_1011_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_snd_1009_);
v___x_1020_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_apply_2(v_toPure_1002_, lean_box(0), v___x_1020_);
return v___x_1021_;
}
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v_snd_1028_; lean_object* v_initialMask_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___x_6132__overap_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_a_1027_ = lean_ctor_get(v_fst_1008_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v_fst_1008_, 1);
v_snd_1028_ = lean_ctor_get(v_____x_1007_, 1);
lean_inc(v_snd_1028_);
lean_dec_ref(v_____x_1007_);
v_initialMask_1029_ = lean_ctor_get(v_a_1027_, 0);
lean_inc_ref(v_initialMask_1029_);
lean_dec(v_a_1027_);
v___x_1030_ = lean_array_get_size(v_initialMask_1029_);
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_box(0);
lean_inc_n(v_toPure_1002_, 2);
v___f_1033_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1033_, 0, v_toPure_1002_);
lean_closure_set(v___f_1033_, 1, v___x_1032_);
v___x_1034_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0));
v___f_1035_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1035_, 0, v_toPure_1002_);
lean_closure_set(v___f_1035_, 1, v___x_1034_);
lean_closure_set(v___f_1035_, 2, v___x_1032_);
lean_inc_n(v_toBind_1004_, 2);
lean_inc_ref(v_inst_1003_);
v___f_1036_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_1036_, 0, v_inst_1003_);
lean_closure_set(v___f_1036_, 1, v_toBind_1004_);
lean_closure_set(v___f_1036_, 2, v___f_1035_);
v___f_1037_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed), 14, 8);
lean_closure_set(v___f_1037_, 0, v___x_1030_);
lean_closure_set(v___f_1037_, 1, v_toPure_1002_);
lean_closure_set(v___f_1037_, 2, v_toBind_1004_);
lean_closure_set(v___f_1037_, 3, v___f_1005_);
lean_closure_set(v___f_1037_, 4, v_initialMask_1029_);
lean_closure_set(v___f_1037_, 5, v___f_1036_);
lean_closure_set(v___f_1037_, 6, v_inst_1003_);
lean_closure_set(v___f_1037_, 7, v___x_1032_);
v___x_6132__overap_1038_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1037_, v___x_1031_, v___x_1034_, lean_box(0));
lean_inc_ref(v_a_1006_);
v___x_1039_ = lean_apply_2(v___x_6132__overap_1038_, v_a_1006_, v_snd_1028_);
v___x_1040_ = lean_apply_4(v_toBind_1004_, lean_box(0), lean_box(0), v___x_1039_, v___f_1033_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed(lean_object* v_toPure_1041_, lean_object* v_inst_1042_, lean_object* v_toBind_1043_, lean_object* v___f_1044_, lean_object* v_a_1045_, lean_object* v_____x_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(v_toPure_1041_, v_inst_1042_, v_toBind_1043_, v___f_1044_, v_a_1045_, v_____x_1046_);
lean_dec_ref(v_a_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(lean_object* v_inst_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_toApplicative_1051_; lean_object* v_toBind_1052_; lean_object* v_toPure_1053_; lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_toApplicative_1051_ = lean_ctor_get(v_inst_1048_, 0);
v_toBind_1052_ = lean_ctor_get(v_inst_1048_, 1);
lean_inc_n(v_toBind_1052_, 2);
v_toPure_1053_ = lean_ctor_get(v_toApplicative_1051_, 1);
lean_inc_n(v_toPure_1053_, 3);
v___f_1054_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1054_, 0, v_toPure_1053_);
lean_inc_ref_n(v_a_1049_, 2);
v___f_1055_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_1055_, 0, v_toPure_1053_);
lean_closure_set(v___f_1055_, 1, v_inst_1048_);
lean_closure_set(v___f_1055_, 2, v_toBind_1052_);
lean_closure_set(v___f_1055_, 3, v___f_1054_);
lean_closure_set(v___f_1055_, 4, v_a_1049_);
v___x_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1056_, 0, v_a_1049_);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v_a_1050_);
v___x_1058_ = lean_apply_2(v_toPure_1053_, lean_box(0), v___x_1057_);
v___x_1059_ = lean_apply_4(v_toBind_1052_, lean_box(0), lean_box(0), v___x_1058_, v___f_1055_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___boxed(lean_object* v_inst_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1060_, v_a_1061_, v_a_1062_);
lean_dec_ref(v_a_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(lean_object* v_m_1064_, lean_object* v_inst_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1065_, v_a_1066_, v_a_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___boxed(lean_object* v_m_1069_, lean_object* v_inst_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(v_m_1069_, v_inst_1070_, v_a_1071_, v_a_1072_);
lean_dec_ref(v_a_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0(lean_object* v_toPure_1076_, lean_object* v_____x_1077_){
_start:
{
lean_object* v_fst_1078_; 
v_fst_1078_ = lean_ctor_get(v_____x_1077_, 0);
lean_inc(v_fst_1078_);
if (lean_obj_tag(v_fst_1078_) == 0)
{
lean_object* v_snd_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1095_; 
v_snd_1079_ = lean_ctor_get(v_____x_1077_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_____x_1077_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v_____x_1077_, 0);
lean_dec(v_unused_1096_);
v___x_1081_ = v_____x_1077_;
v_isShared_1082_ = v_isSharedCheck_1095_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_snd_1079_);
lean_dec(v_____x_1077_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1095_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1094_; 
v_a_1083_ = lean_ctor_get(v_fst_1078_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_fst_1078_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1085_ = v_fst_1078_;
v_isShared_1086_ = v_isSharedCheck_1094_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v_fst_1078_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1094_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1090_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1088_);
v___x_1090_ = v___x_1081_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_snd_1079_);
v___x_1090_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_apply_2(v_toPure_1076_, lean_box(0), v___x_1090_);
return v___x_1091_;
}
}
}
}
}
else
{
lean_object* v_snd_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref_known(v_fst_1078_, 1);
v_snd_1097_ = lean_ctor_get(v_____x_1077_, 1);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_____x_1077_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; 
v_unused_1107_ = lean_ctor_get(v_____x_1077_, 0);
lean_dec(v_unused_1107_);
v___x_1099_ = v_____x_1077_;
v_isShared_1100_ = v_isSharedCheck_1106_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_snd_1097_);
lean_dec(v_____x_1077_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1106_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1101_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0));
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1101_);
v___x_1103_ = v___x_1099_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_snd_1097_);
v___x_1103_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_apply_2(v_toPure_1076_, lean_box(0), v___x_1103_);
return v___x_1104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1(lean_object* v_toPure_1108_, lean_object* v_____x_1109_){
_start:
{
lean_object* v_fst_1110_; 
v_fst_1110_ = lean_ctor_get(v_____x_1109_, 0);
lean_inc(v_fst_1110_);
if (lean_obj_tag(v_fst_1110_) == 0)
{
lean_object* v_snd_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1127_; 
v_snd_1111_ = lean_ctor_get(v_____x_1109_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_____x_1109_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v_____x_1109_, 0);
lean_dec(v_unused_1128_);
v___x_1113_ = v_____x_1109_;
v_isShared_1114_ = v_isSharedCheck_1127_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_snd_1111_);
lean_dec(v_____x_1109_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1127_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1126_; 
v_a_1115_ = lean_ctor_get(v_fst_1110_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_fst_1110_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1117_ = v_fst_1110_;
v_isShared_1118_ = v_isSharedCheck_1126_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v_fst_1110_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1126_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1122_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1120_);
v___x_1122_ = v___x_1113_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_snd_1111_);
v___x_1122_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_apply_2(v_toPure_1108_, lean_box(0), v___x_1122_);
return v___x_1123_;
}
}
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1175_; 
v_a_1129_ = lean_ctor_get(v_fst_1110_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_fst_1110_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1131_ = v_fst_1110_;
v_isShared_1132_ = v_isSharedCheck_1175_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v_fst_1110_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1175_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
if (lean_obj_tag(v_a_1129_) == 0)
{
lean_object* v_snd_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1152_; 
v_snd_1133_ = lean_ctor_get(v_____x_1109_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_____x_1109_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; 
v_unused_1153_ = lean_ctor_get(v_____x_1109_, 0);
lean_dec(v_unused_1153_);
v___x_1135_ = v_____x_1109_;
v_isShared_1136_ = v_isSharedCheck_1152_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_snd_1133_);
lean_dec(v_____x_1109_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1152_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1151_; 
v_a_1137_ = lean_ctor_get(v_a_1129_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_a_1129_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1139_ = v_a_1129_;
v_isShared_1140_ = v_isSharedCheck_1151_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v_a_1129_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1151_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set_tag(v___x_1139_, 1);
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1144_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1142_);
v___x_1144_ = v___x_1131_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1144_);
v___x_1146_ = v___x_1135_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_snd_1133_);
v___x_1146_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_apply_2(v_toPure_1108_, lean_box(0), v___x_1146_);
return v___x_1147_;
}
}
}
}
}
}
else
{
lean_object* v_snd_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1173_; 
v_snd_1154_ = lean_ctor_get(v_____x_1109_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_____x_1109_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; 
v_unused_1174_ = lean_ctor_get(v_____x_1109_, 0);
lean_dec(v_unused_1174_);
v___x_1156_ = v_____x_1109_;
v_isShared_1157_ = v_isSharedCheck_1173_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_snd_1154_);
lean_dec(v_____x_1109_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1173_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1172_; 
v_a_1158_ = lean_ctor_get(v_a_1129_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_a_1129_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1160_ = v_a_1129_;
v_isShared_1161_ = v_isSharedCheck_1172_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v_a_1129_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1172_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set_tag(v___x_1160_, 0);
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1163_);
v___x_1165_ = v___x_1131_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v___x_1165_);
v___x_1167_ = v___x_1156_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_snd_1154_);
v___x_1167_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_apply_2(v_toPure_1108_, lean_box(0), v___x_1167_);
return v___x_1168_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2(lean_object* v_toPure_1176_, lean_object* v___x_1177_, lean_object* v_____x_1178_){
_start:
{
lean_object* v_fst_1179_; 
v_fst_1179_ = lean_ctor_get(v_____x_1178_, 0);
lean_inc(v_fst_1179_);
if (lean_obj_tag(v_fst_1179_) == 0)
{
lean_object* v_snd_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1196_; 
lean_dec(v___x_1177_);
v_snd_1180_ = lean_ctor_get(v_____x_1178_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_____x_1178_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v_____x_1178_, 0);
lean_dec(v_unused_1197_);
v___x_1182_ = v_____x_1178_;
v_isShared_1183_ = v_isSharedCheck_1196_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_snd_1180_);
lean_dec(v_____x_1178_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1196_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1195_; 
v_a_1184_ = lean_ctor_get(v_fst_1179_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_fst_1179_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1186_ = v_fst_1179_;
v_isShared_1187_ = v_isSharedCheck_1195_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v_fst_1179_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1195_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1191_; 
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1189_);
v___x_1191_ = v___x_1182_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_snd_1180_);
v___x_1191_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_apply_2(v_toPure_1176_, lean_box(0), v___x_1191_);
return v___x_1192_;
}
}
}
}
}
else
{
lean_object* v_snd_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1215_; 
v_snd_1198_ = lean_ctor_get(v_____x_1178_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_____x_1178_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v_____x_1178_, 0);
lean_dec(v_unused_1216_);
v___x_1200_ = v_____x_1178_;
v_isShared_1201_ = v_isSharedCheck_1215_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_snd_1198_);
lean_dec(v_____x_1178_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1215_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1213_; 
v_isSharedCheck_1213_ = !lean_is_exclusive(v_fst_1179_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v_fst_1179_, 0);
lean_dec(v_unused_1214_);
v___x_1203_ = v_fst_1179_;
v_isShared_1204_ = v_isSharedCheck_1213_;
goto v_resetjp_1202_;
}
else
{
lean_dec(v_fst_1179_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1213_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1177_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1205_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1209_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1207_);
v___x_1209_ = v___x_1200_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_snd_1198_);
v___x_1209_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_apply_2(v_toPure_1176_, lean_box(0), v___x_1209_);
return v___x_1210_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(lean_object* v_toPure_1217_, lean_object* v___x_1218_, lean_object* v_inst_1219_, lean_object* v_toBind_1220_, lean_object* v___f_1221_, lean_object* v___x_1222_, lean_object* v_____x_1223_){
_start:
{
lean_object* v_fst_1224_; 
v_fst_1224_ = lean_ctor_get(v_____x_1223_, 0);
lean_inc(v_fst_1224_);
if (lean_obj_tag(v_fst_1224_) == 0)
{
lean_object* v_snd_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v___x_1222_);
lean_dec(v___f_1221_);
lean_dec(v_toBind_1220_);
lean_dec_ref(v_inst_1219_);
v_snd_1225_ = lean_ctor_get(v_____x_1223_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_____x_1223_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v_____x_1223_, 0);
lean_dec(v_unused_1242_);
v___x_1227_ = v_____x_1223_;
v_isShared_1228_ = v_isSharedCheck_1241_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_snd_1225_);
lean_dec(v_____x_1223_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1241_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1240_; 
v_a_1229_ = lean_ctor_get(v_fst_1224_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_fst_1224_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1231_ = v_fst_1224_;
v_isShared_1232_ = v_isSharedCheck_1240_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v_fst_1224_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1240_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1236_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1234_);
v___x_1236_ = v___x_1227_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_snd_1225_);
v___x_1236_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_apply_2(v_toPure_1217_, lean_box(0), v___x_1236_);
return v___x_1237_;
}
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1265_; 
v_a_1243_ = lean_ctor_get(v_fst_1224_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_fst_1224_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1245_ = v_fst_1224_;
v_isShared_1246_ = v_isSharedCheck_1265_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v_fst_1224_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1265_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
uint8_t v___x_1247_; 
v___x_1247_ = lean_unbox(v_a_1243_);
lean_dec(v_a_1243_);
if (v___x_1247_ == 0)
{
lean_object* v_snd_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_del_object(v___x_1245_);
lean_dec(v___x_1222_);
lean_dec(v_toPure_1217_);
v_snd_1248_ = lean_ctor_get(v_____x_1223_, 1);
lean_inc(v_snd_1248_);
lean_dec_ref(v_____x_1223_);
v___x_1249_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v___x_1218_, v_inst_1219_, v_snd_1248_);
v___x_1250_ = lean_apply_4(v_toBind_1220_, lean_box(0), lean_box(0), v___x_1249_, v___f_1221_);
return v___x_1250_;
}
else
{
lean_object* v_snd_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v___f_1221_);
lean_dec(v_toBind_1220_);
lean_dec_ref(v_inst_1219_);
v_snd_1251_ = lean_ctor_get(v_____x_1223_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_____x_1223_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v_____x_1223_, 0);
lean_dec(v_unused_1264_);
v___x_1253_ = v_____x_1223_;
v_isShared_1254_ = v_isSharedCheck_1263_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_snd_1251_);
lean_dec(v_____x_1223_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1263_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1222_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1255_);
v___x_1257_ = v___x_1245_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1259_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1257_);
v___x_1259_ = v___x_1253_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_snd_1251_);
v___x_1259_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_apply_2(v_toPure_1217_, lean_box(0), v___x_1259_);
return v___x_1260_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed(lean_object* v_toPure_1266_, lean_object* v___x_1267_, lean_object* v_inst_1268_, lean_object* v_toBind_1269_, lean_object* v___f_1270_, lean_object* v___x_1271_, lean_object* v_____x_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(v_toPure_1266_, v___x_1267_, v_inst_1268_, v_toBind_1269_, v___f_1270_, v___x_1271_, v_____x_1272_);
lean_dec(v___x_1267_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(lean_object* v_toPure_1274_, lean_object* v_inst_1275_, lean_object* v___y_1276_, lean_object* v_toBind_1277_, lean_object* v___f_1278_, lean_object* v_____x_1279_){
_start:
{
lean_object* v_fst_1280_; 
v_fst_1280_ = lean_ctor_get(v_____x_1279_, 0);
lean_inc(v_fst_1280_);
if (lean_obj_tag(v_fst_1280_) == 0)
{
lean_object* v_snd_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v___f_1278_);
lean_dec(v_toBind_1277_);
lean_dec_ref(v_inst_1275_);
v_snd_1281_ = lean_ctor_get(v_____x_1279_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_____x_1279_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v_____x_1279_, 0);
lean_dec(v_unused_1298_);
v___x_1283_ = v_____x_1279_;
v_isShared_1284_ = v_isSharedCheck_1297_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_snd_1281_);
lean_dec(v_____x_1279_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1297_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1296_; 
v_a_1285_ = lean_ctor_get(v_fst_1280_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_fst_1280_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1287_ = v_fst_1280_;
v_isShared_1288_ = v_isSharedCheck_1296_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v_fst_1280_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1296_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1292_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1290_);
v___x_1292_ = v___x_1283_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_snd_1281_);
v___x_1292_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_apply_2(v_toPure_1274_, lean_box(0), v___x_1292_);
return v___x_1293_;
}
}
}
}
}
else
{
lean_object* v_snd_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec_ref_known(v_fst_1280_, 1);
lean_dec(v_toPure_1274_);
v_snd_1299_ = lean_ctor_get(v_____x_1279_, 1);
lean_inc(v_snd_1299_);
lean_dec_ref(v_____x_1279_);
v___x_1300_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_1275_, v___y_1276_, v_snd_1299_);
v___x_1301_ = lean_apply_4(v_toBind_1277_, lean_box(0), lean_box(0), v___x_1300_, v___f_1278_);
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed(lean_object* v_toPure_1302_, lean_object* v_inst_1303_, lean_object* v___y_1304_, lean_object* v_toBind_1305_, lean_object* v___f_1306_, lean_object* v_____x_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(v_toPure_1302_, v_inst_1303_, v___y_1304_, v_toBind_1305_, v___f_1306_, v_____x_1307_);
lean_dec_ref(v___y_1304_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(lean_object* v_toPure_1309_, lean_object* v___x_1310_, lean_object* v___x_1311_, lean_object* v_inst_1312_, lean_object* v_toBind_1313_, lean_object* v___f_1314_, lean_object* v___y_1315_, lean_object* v_____x_1316_){
_start:
{
lean_object* v_fst_1317_; 
v_fst_1317_ = lean_ctor_get(v_____x_1316_, 0);
lean_inc(v_fst_1317_);
if (lean_obj_tag(v_fst_1317_) == 0)
{
lean_object* v_snd_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v___f_1314_);
lean_dec(v_toBind_1313_);
lean_dec_ref(v_inst_1312_);
lean_dec(v___x_1311_);
v_snd_1318_ = lean_ctor_get(v_____x_1316_, 1);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_____x_1316_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; 
v_unused_1335_ = lean_ctor_get(v_____x_1316_, 0);
lean_dec(v_unused_1335_);
v___x_1320_ = v_____x_1316_;
v_isShared_1321_ = v_isSharedCheck_1334_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_snd_1318_);
lean_dec(v_____x_1316_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1334_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1333_; 
v_a_1322_ = lean_ctor_get(v_fst_1317_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_fst_1317_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1324_ = v_fst_1317_;
v_isShared_1325_ = v_isSharedCheck_1333_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v_fst_1317_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1333_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1329_; 
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1327_);
v___x_1329_ = v___x_1320_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_snd_1318_);
v___x_1329_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_apply_2(v_toPure_1309_, lean_box(0), v___x_1329_);
return v___x_1330_;
}
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v_snd_1337_; lean_object* v_added_1338_; lean_object* v___x_1339_; lean_object* v___f_1340_; lean_object* v___f_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_a_1336_ = lean_ctor_get(v_fst_1317_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v_fst_1317_, 1);
v_snd_1337_ = lean_ctor_get(v_____x_1316_, 1);
lean_inc(v_snd_1337_);
lean_dec_ref(v_____x_1316_);
v_added_1338_ = lean_ctor_get(v_a_1336_, 1);
lean_inc_ref(v_added_1338_);
lean_dec(v_a_1336_);
v___x_1339_ = lean_array_get(v___x_1310_, v_added_1338_, v___x_1311_);
lean_dec_ref(v_added_1338_);
lean_inc_n(v_toBind_1313_, 2);
lean_inc_ref_n(v_inst_1312_, 2);
lean_inc(v___x_1339_);
lean_inc(v_toPure_1309_);
v___f_1340_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1340_, 0, v_toPure_1309_);
lean_closure_set(v___f_1340_, 1, v___x_1339_);
lean_closure_set(v___f_1340_, 2, v_inst_1312_);
lean_closure_set(v___f_1340_, 3, v_toBind_1313_);
lean_closure_set(v___f_1340_, 4, v___f_1314_);
lean_closure_set(v___f_1340_, 5, v___x_1311_);
lean_inc_ref(v___y_1315_);
v___f_1341_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_1341_, 0, v_toPure_1309_);
lean_closure_set(v___f_1341_, 1, v_inst_1312_);
lean_closure_set(v___f_1341_, 2, v___y_1315_);
lean_closure_set(v___f_1341_, 3, v_toBind_1313_);
lean_closure_set(v___f_1341_, 4, v___f_1340_);
v___x_1342_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v___x_1339_, v_inst_1312_, v_snd_1337_);
lean_dec(v___x_1339_);
v___x_1343_ = lean_apply_4(v_toBind_1313_, lean_box(0), lean_box(0), v___x_1342_, v___f_1341_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed(lean_object* v_toPure_1344_, lean_object* v___x_1345_, lean_object* v___x_1346_, lean_object* v_inst_1347_, lean_object* v_toBind_1348_, lean_object* v___f_1349_, lean_object* v___y_1350_, lean_object* v_____x_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(v_toPure_1344_, v___x_1345_, v___x_1346_, v_inst_1347_, v_toBind_1348_, v___f_1349_, v___y_1350_, v_____x_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___x_1345_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7(lean_object* v_toPure_1353_, lean_object* v_toBind_1354_, lean_object* v___f_1355_, lean_object* v___x_1356_, lean_object* v___x_1357_, lean_object* v_inst_1358_, lean_object* v_b_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = lean_nat_dec_lt(v___x_1362_, v_b_1359_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v_inst_1358_);
lean_dec(v___x_1357_);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v_b_1359_);
v___x_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v___y_1361_);
v___x_1367_ = lean_apply_2(v_toPure_1353_, lean_box(0), v___x_1366_);
v___x_1368_ = lean_apply_4(v_toBind_1354_, lean_box(0), lean_box(0), v___x_1367_, v___f_1355_);
return v___x_1368_;
}
else
{
lean_object* v___x_1369_; lean_object* v___f_1370_; lean_object* v___f_1371_; lean_object* v___f_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1369_ = lean_nat_sub(v_b_1359_, v___x_1356_);
lean_dec(v_b_1359_);
lean_inc(v___x_1369_);
lean_inc_n(v_toPure_1353_, 3);
v___f_1370_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1370_, 0, v_toPure_1353_);
lean_closure_set(v___f_1370_, 1, v___x_1369_);
lean_inc_ref(v___y_1360_);
lean_inc_n(v_toBind_1354_, 3);
v___f_1371_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1371_, 0, v_toPure_1353_);
lean_closure_set(v___f_1371_, 1, v___x_1357_);
lean_closure_set(v___f_1371_, 2, v___x_1369_);
lean_closure_set(v___f_1371_, 3, v_inst_1358_);
lean_closure_set(v___f_1371_, 4, v_toBind_1354_);
lean_closure_set(v___f_1371_, 5, v___f_1370_);
lean_closure_set(v___f_1371_, 6, v___y_1360_);
v___f_1372_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1372_, 0, v_toPure_1353_);
lean_inc_ref(v___y_1361_);
v___x_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___y_1361_);
lean_ctor_set(v___x_1373_, 1, v___y_1361_);
v___x_1374_ = lean_apply_2(v_toPure_1353_, lean_box(0), v___x_1373_);
v___x_1375_ = lean_apply_4(v_toBind_1354_, lean_box(0), lean_box(0), v___x_1374_, v___f_1372_);
v___x_1376_ = lean_apply_4(v_toBind_1354_, lean_box(0), lean_box(0), v___x_1375_, v___f_1371_);
v___x_1377_ = lean_apply_4(v_toBind_1354_, lean_box(0), lean_box(0), v___x_1376_, v___f_1355_);
return v___x_1377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed(lean_object* v_toPure_1378_, lean_object* v_toBind_1379_, lean_object* v___f_1380_, lean_object* v___x_1381_, lean_object* v___x_1382_, lean_object* v_inst_1383_, lean_object* v_b_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7(v_toPure_1378_, v_toBind_1379_, v___f_1380_, v___x_1381_, v___x_1382_, v_inst_1383_, v_b_1384_, v___y_1385_, v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___x_1381_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(lean_object* v_toPure_1388_, lean_object* v_toBind_1389_, lean_object* v___f_1390_, lean_object* v___x_1391_, lean_object* v_inst_1392_, lean_object* v___x_1393_, lean_object* v_a_1394_, lean_object* v___f_1395_, lean_object* v_____x_1396_){
_start:
{
lean_object* v_fst_1397_; 
v_fst_1397_ = lean_ctor_get(v_____x_1396_, 0);
lean_inc(v_fst_1397_);
if (lean_obj_tag(v_fst_1397_) == 0)
{
lean_object* v_snd_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v___f_1395_);
lean_dec_ref(v___x_1393_);
lean_dec_ref(v_inst_1392_);
lean_dec(v___x_1391_);
lean_dec(v___f_1390_);
lean_dec(v_toBind_1389_);
v_snd_1398_ = lean_ctor_get(v_____x_1396_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_____x_1396_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v_____x_1396_, 0);
lean_dec(v_unused_1415_);
v___x_1400_ = v_____x_1396_;
v_isShared_1401_ = v_isSharedCheck_1414_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_snd_1398_);
lean_dec(v_____x_1396_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1414_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1413_; 
v_a_1402_ = lean_ctor_get(v_fst_1397_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_fst_1397_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1404_ = v_fst_1397_;
v_isShared_1405_ = v_isSharedCheck_1413_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v_fst_1397_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1413_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1409_; 
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1407_);
v___x_1409_ = v___x_1400_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_snd_1398_);
v___x_1409_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_apply_2(v_toPure_1388_, lean_box(0), v___x_1409_);
return v___x_1410_;
}
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v_snd_1417_; lean_object* v_added_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___f_1421_; lean_object* v___x_1422_; lean_object* v___x_5974__overap_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_a_1416_ = lean_ctor_get(v_fst_1397_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v_fst_1397_, 1);
v_snd_1417_ = lean_ctor_get(v_____x_1396_, 1);
lean_inc(v_snd_1417_);
lean_dec_ref(v_____x_1396_);
v_added_1418_ = lean_ctor_get(v_a_1416_, 1);
lean_inc_ref(v_added_1418_);
lean_dec(v_a_1416_);
v___x_1419_ = lean_array_get_size(v_added_1418_);
lean_dec_ref(v_added_1418_);
v___x_1420_ = lean_unsigned_to_nat(1u);
lean_inc(v_toBind_1389_);
v___f_1421_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed), 9, 6);
lean_closure_set(v___f_1421_, 0, v_toPure_1388_);
lean_closure_set(v___f_1421_, 1, v_toBind_1389_);
lean_closure_set(v___f_1421_, 2, v___f_1390_);
lean_closure_set(v___f_1421_, 3, v___x_1420_);
lean_closure_set(v___f_1421_, 4, v___x_1391_);
lean_closure_set(v___f_1421_, 5, v_inst_1392_);
v___x_1422_ = lean_nat_sub(v___x_1419_, v___x_1420_);
v___x_5974__overap_1423_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_1393_, v___f_1421_, v___x_1422_);
lean_inc_ref(v_a_1394_);
v___x_1424_ = lean_apply_2(v___x_5974__overap_1423_, v_a_1394_, v_snd_1417_);
v___x_1425_ = lean_apply_4(v_toBind_1389_, lean_box(0), lean_box(0), v___x_1424_, v___f_1395_);
return v___x_1425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed(lean_object* v_toPure_1426_, lean_object* v_toBind_1427_, lean_object* v___f_1428_, lean_object* v___x_1429_, lean_object* v_inst_1430_, lean_object* v___x_1431_, lean_object* v_a_1432_, lean_object* v___f_1433_, lean_object* v_____x_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(v_toPure_1426_, v_toBind_1427_, v___f_1428_, v___x_1429_, v_inst_1430_, v___x_1431_, v_a_1432_, v___f_1433_, v_____x_1434_);
lean_dec_ref(v_a_1432_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(lean_object* v_inst_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___f_1439_; lean_object* v___f_1440_; lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___f_1449_; lean_object* v___f_1450_; lean_object* v___f_1451_; lean_object* v___f_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_toApplicative_1460_; lean_object* v_toBind_1461_; lean_object* v_toPure_1462_; lean_object* v___f_1463_; lean_object* v___f_1464_; lean_object* v___x_1465_; lean_object* v___f_1466_; lean_object* v___f_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_inc_ref_n(v_inst_1436_, 7);
v___f_1439_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1439_, 0, v_inst_1436_);
v___f_1440_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1440_, 0, v_inst_1436_);
v___f_1441_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1441_, 0, v_inst_1436_);
v___f_1442_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1442_, 0, v_inst_1436_);
v___x_1443_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1443_, 0, lean_box(0));
lean_closure_set(v___x_1443_, 1, lean_box(0));
lean_closure_set(v___x_1443_, 2, v_inst_1436_);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
lean_ctor_set(v___x_1444_, 1, v___f_1439_);
v___x_1445_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1445_, 0, lean_box(0));
lean_closure_set(v___x_1445_, 1, lean_box(0));
lean_closure_set(v___x_1445_, 2, v_inst_1436_);
v___x_1446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
lean_ctor_set(v___x_1446_, 2, v___f_1440_);
lean_ctor_set(v___x_1446_, 3, v___f_1441_);
lean_ctor_set(v___x_1446_, 4, v___f_1442_);
v___x_1447_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1447_, 0, lean_box(0));
lean_closure_set(v___x_1447_, 1, lean_box(0));
lean_closure_set(v___x_1447_, 2, v_inst_1436_);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1446_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
lean_inc_ref_n(v___x_1448_, 6);
v___f_1449_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1449_, 0, v___x_1448_);
v___f_1450_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1450_, 0, v___x_1448_);
v___f_1451_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1451_, 0, v___x_1448_);
v___f_1452_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1452_, 0, v___x_1448_);
v___x_1453_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1453_, 0, lean_box(0));
lean_closure_set(v___x_1453_, 1, lean_box(0));
lean_closure_set(v___x_1453_, 2, v___x_1448_);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v___f_1449_);
v___x_1455_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1455_, 0, lean_box(0));
lean_closure_set(v___x_1455_, 1, lean_box(0));
lean_closure_set(v___x_1455_, 2, v___x_1448_);
v___x_1456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
lean_ctor_set(v___x_1456_, 2, v___f_1450_);
lean_ctor_set(v___x_1456_, 3, v___f_1451_);
lean_ctor_set(v___x_1456_, 4, v___f_1452_);
v___x_1457_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1457_, 0, lean_box(0));
lean_closure_set(v___x_1457_, 1, lean_box(0));
lean_closure_set(v___x_1457_, 2, v___x_1448_);
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = l_ReaderT_instMonad___redArg(v___x_1458_);
v_toApplicative_1460_ = lean_ctor_get(v_inst_1436_, 0);
v_toBind_1461_ = lean_ctor_get(v_inst_1436_, 1);
lean_inc_n(v_toBind_1461_, 3);
v_toPure_1462_ = lean_ctor_get(v_toApplicative_1460_, 1);
lean_inc_n(v_toPure_1462_, 5);
v___f_1463_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1463_, 0, v_toPure_1462_);
v___f_1464_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1464_, 0, v_toPure_1462_);
v___x_1465_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1437_);
v___f_1466_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed), 9, 8);
lean_closure_set(v___f_1466_, 0, v_toPure_1462_);
lean_closure_set(v___f_1466_, 1, v_toBind_1461_);
lean_closure_set(v___f_1466_, 2, v___f_1464_);
lean_closure_set(v___f_1466_, 3, v___x_1465_);
lean_closure_set(v___f_1466_, 4, v_inst_1436_);
lean_closure_set(v___f_1466_, 5, v___x_1459_);
lean_closure_set(v___f_1466_, 6, v_a_1437_);
lean_closure_set(v___f_1466_, 7, v___f_1463_);
v___f_1467_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1467_, 0, v_toPure_1462_);
lean_inc_ref(v_a_1438_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_a_1438_);
lean_ctor_set(v___x_1468_, 1, v_a_1438_);
v___x_1469_ = lean_apply_2(v_toPure_1462_, lean_box(0), v___x_1468_);
v___x_1470_ = lean_apply_4(v_toBind_1461_, lean_box(0), lean_box(0), v___x_1469_, v___f_1467_);
v___x_1471_ = lean_apply_4(v_toBind_1461_, lean_box(0), lean_box(0), v___x_1470_, v___f_1466_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___boxed(lean_object* v_inst_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1472_, v_a_1473_, v_a_1474_);
lean_dec_ref(v_a_1473_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(lean_object* v_m_1476_, lean_object* v_inst_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1477_, v_a_1478_, v_a_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___boxed(lean_object* v_m_1481_, lean_object* v_inst_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(v_m_1481_, v_inst_1482_, v_a_1483_, v_a_1484_);
lean_dec_ref(v_a_1483_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(lean_object* v_toApplicative_1486_, lean_object* v_inst_1487_, lean_object* v_a_1488_, lean_object* v_____x_1489_){
_start:
{
lean_object* v_fst_1490_; 
v_fst_1490_ = lean_ctor_get(v_____x_1489_, 0);
lean_inc(v_fst_1490_);
if (lean_obj_tag(v_fst_1490_) == 0)
{
lean_object* v_snd_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1508_; 
lean_dec_ref(v_inst_1487_);
v_snd_1491_ = lean_ctor_get(v_____x_1489_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_____x_1489_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v_____x_1489_, 0);
lean_dec(v_unused_1509_);
v___x_1493_ = v_____x_1489_;
v_isShared_1494_ = v_isSharedCheck_1508_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_snd_1491_);
lean_dec(v_____x_1489_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1508_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1507_; 
v_a_1495_ = lean_ctor_get(v_fst_1490_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_fst_1490_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1497_ = v_fst_1490_;
v_isShared_1498_ = v_isSharedCheck_1507_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v_fst_1490_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1507_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_toPure_1499_; lean_object* v___x_1501_; 
v_toPure_1499_ = lean_ctor_get(v_toApplicative_1486_, 1);
lean_inc(v_toPure_1499_);
lean_dec_ref(v_toApplicative_1486_);
if (v_isShared_1498_ == 0)
{
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1495_);
v___x_1501_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1503_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1501_);
v___x_1503_ = v___x_1493_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_snd_1491_);
v___x_1503_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_apply_2(v_toPure_1499_, lean_box(0), v___x_1503_);
return v___x_1504_;
}
}
}
}
}
else
{
lean_object* v_a_1510_; uint8_t v_found_1511_; 
v_a_1510_ = lean_ctor_get(v_fst_1490_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v_fst_1490_, 1);
v_found_1511_ = lean_ctor_get_uint8(v_a_1510_, sizeof(void*)*3);
lean_dec(v_a_1510_);
if (v_found_1511_ == 0)
{
lean_object* v_snd_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1522_; 
lean_dec_ref(v_inst_1487_);
v_snd_1512_ = lean_ctor_get(v_____x_1489_, 1);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_____x_1489_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v_____x_1489_, 0);
lean_dec(v_unused_1523_);
v___x_1514_ = v_____x_1489_;
v_isShared_1515_ = v_isSharedCheck_1522_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_snd_1512_);
lean_dec(v_____x_1489_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1522_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v_toPure_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
v_toPure_1516_ = lean_ctor_get(v_toApplicative_1486_, 1);
lean_inc(v_toPure_1516_);
lean_dec_ref(v_toApplicative_1486_);
v___x_1517_ = ((lean_object*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0));
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1517_);
v___x_1519_ = v___x_1514_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_snd_1512_);
v___x_1519_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_apply_2(v_toPure_1516_, lean_box(0), v___x_1519_);
return v___x_1520_;
}
}
}
else
{
lean_object* v_snd_1524_; lean_object* v___x_1525_; 
lean_dec_ref(v_toApplicative_1486_);
v_snd_1524_ = lean_ctor_get(v_____x_1489_, 1);
lean_inc(v_snd_1524_);
lean_dec_ref(v_____x_1489_);
v___x_1525_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_1487_, v_a_1488_, v_snd_1524_);
return v___x_1525_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed(lean_object* v_toApplicative_1526_, lean_object* v_inst_1527_, lean_object* v_a_1528_, lean_object* v_____x_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(v_toApplicative_1526_, v_inst_1527_, v_a_1528_, v_____x_1529_);
lean_dec_ref(v_a_1528_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2(lean_object* v_toApplicative_1531_, lean_object* v_toBind_1532_, lean_object* v___f_1533_, lean_object* v_____x_1534_){
_start:
{
lean_object* v_fst_1535_; 
v_fst_1535_ = lean_ctor_get(v_____x_1534_, 0);
if (lean_obj_tag(v_fst_1535_) == 0)
{
lean_object* v_toPure_1536_; lean_object* v___x_1537_; 
lean_dec(v___f_1533_);
lean_dec(v_toBind_1532_);
v_toPure_1536_ = lean_ctor_get(v_toApplicative_1531_, 1);
lean_inc(v_toPure_1536_);
lean_dec_ref(v_toApplicative_1531_);
v___x_1537_ = lean_apply_2(v_toPure_1536_, lean_box(0), v_____x_1534_);
return v___x_1537_;
}
else
{
lean_object* v_snd_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1550_; 
v_snd_1538_ = lean_ctor_get(v_____x_1534_, 1);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_____x_1534_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_____x_1534_, 0);
lean_dec(v_unused_1551_);
v___x_1540_ = v_____x_1534_;
v_isShared_1541_ = v_isSharedCheck_1550_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_snd_1538_);
lean_dec(v_____x_1534_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1550_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_toPure_1542_; lean_object* v___f_1543_; lean_object* v___x_1545_; 
v_toPure_1542_ = lean_ctor_get(v_toApplicative_1531_, 1);
lean_inc_n(v_toPure_1542_, 2);
lean_dec_ref(v_toApplicative_1531_);
v___f_1543_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5), 2, 1);
lean_closure_set(v___f_1543_, 0, v_toPure_1542_);
lean_inc(v_snd_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v_snd_1538_);
v___x_1545_ = v___x_1540_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_snd_1538_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_snd_1538_);
v___x_1545_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = lean_apply_2(v_toPure_1542_, lean_box(0), v___x_1545_);
lean_inc(v_toBind_1532_);
v___x_1547_ = lean_apply_4(v_toBind_1532_, lean_box(0), lean_box(0), v___x_1546_, v___f_1543_);
v___x_1548_ = lean_apply_4(v_toBind_1532_, lean_box(0), lean_box(0), v___x_1547_, v___f_1533_);
return v___x_1548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(lean_object* v_inst_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v_toApplicative_1555_; lean_object* v_toBind_1556_; lean_object* v___f_1557_; lean_object* v___f_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_toApplicative_1555_ = lean_ctor_get(v_inst_1552_, 0);
v_toBind_1556_ = lean_ctor_get(v_inst_1552_, 1);
lean_inc_n(v_toBind_1556_, 2);
lean_inc_ref(v_a_1553_);
lean_inc_ref(v_inst_1552_);
lean_inc_ref_n(v_toApplicative_1555_, 2);
v___f_1557_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1557_, 0, v_toApplicative_1555_);
lean_closure_set(v___f_1557_, 1, v_inst_1552_);
lean_closure_set(v___f_1557_, 2, v_a_1553_);
v___f_1558_ = lean_alloc_closure((void*)(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1558_, 0, v_toApplicative_1555_);
lean_closure_set(v___f_1558_, 1, v_toBind_1556_);
lean_closure_set(v___f_1558_, 2, v___f_1557_);
v___x_1559_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(v_inst_1552_, v_a_1553_, v_a_1554_);
v___x_1560_ = lean_apply_4(v_toBind_1556_, lean_box(0), lean_box(0), v___x_1559_, v___f_1558_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___boxed(lean_object* v_inst_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1561_, v_a_1562_, v_a_1563_);
lean_dec_ref(v_a_1562_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(lean_object* v_m_1565_, lean_object* v_inst_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1566_, v_a_1567_, v_a_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___boxed(lean_object* v_m_1570_, lean_object* v_inst_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(v_m_1570_, v_inst_1571_, v_a_1572_, v_a_1573_);
lean_dec_ref(v_a_1572_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0(lean_object* v_toPure_1575_, lean_object* v_____x_1576_){
_start:
{
lean_object* v_snd_1577_; lean_object* v_fst_1578_; lean_object* v_cur_1579_; lean_object* v_numCalls_1580_; uint8_t v_found_1581_; uint8_t v___y_1583_; 
v_snd_1577_ = lean_ctor_get(v_____x_1576_, 1);
v_fst_1578_ = lean_ctor_get(v_____x_1576_, 0);
v_cur_1579_ = lean_ctor_get(v_snd_1577_, 0);
v_numCalls_1580_ = lean_ctor_get(v_snd_1577_, 2);
v_found_1581_ = lean_ctor_get_uint8(v_snd_1577_, sizeof(void*)*3);
if (v_found_1581_ == 0)
{
uint8_t v___x_1586_; 
v___x_1586_ = 0;
v___y_1583_ = v___x_1586_;
goto v___jp_1582_;
}
else
{
if (lean_obj_tag(v_fst_1578_) == 0)
{
uint8_t v___x_1587_; 
v___x_1587_ = 1;
v___y_1583_ = v___x_1587_;
goto v___jp_1582_;
}
else
{
uint8_t v___x_1588_; 
v___x_1588_ = 2;
v___y_1583_ = v___x_1588_;
goto v___jp_1582_;
}
}
v___jp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_inc(v_numCalls_1580_);
lean_inc_ref(v_cur_1579_);
v___x_1584_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1584_, 0, v_cur_1579_);
lean_ctor_set(v___x_1584_, 1, v_numCalls_1580_);
lean_ctor_set_uint8(v___x_1584_, sizeof(void*)*2, v___y_1583_);
v___x_1585_ = lean_apply_2(v_toPure_1575_, lean_box(0), v___x_1584_);
return v___x_1585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed(lean_object* v_toPure_1589_, lean_object* v_____x_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__0(v_toPure_1589_, v_____x_1590_);
lean_dec_ref(v_____x_1590_);
return v_res_1591_;
}
}
lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1(lean_object* v_initialMask_1594_, lean_object* v_test_1595_, lean_object* v_maxCalls_1596_, lean_object* v_inst_1597_, lean_object* v_toBind_1598_, lean_object* v___f_1599_, lean_object* v_toPure_1600_, uint8_t v_____do__lift_1601_){
_start:
{
if (v_____do__lift_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec(v_toPure_1600_);
lean_inc_ref(v_initialMask_1594_);
v___x_1602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1602_, 0, v_initialMask_1594_);
lean_ctor_set(v___x_1602_, 1, v_test_1595_);
lean_ctor_set(v___x_1602_, 2, v_maxCalls_1596_);
v___x_1603_ = ((lean_object*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0));
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1605_, 0, v_initialMask_1594_);
lean_ctor_set(v___x_1605_, 1, v___x_1603_);
lean_ctor_set(v___x_1605_, 2, v___x_1604_);
lean_ctor_set_uint8(v___x_1605_, sizeof(void*)*3, v_____do__lift_1601_);
v___x_1606_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(v_inst_1597_, v___x_1602_, v___x_1605_);
lean_dec_ref_known(v___x_1602_, 3);
v___x_1607_ = lean_apply_4(v_toBind_1598_, lean_box(0), lean_box(0), v___x_1606_, v___f_1599_);
return v___x_1607_;
}
else
{
uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec(v___f_1599_);
lean_dec(v_toBind_1598_);
lean_dec_ref(v_inst_1597_);
lean_dec(v_maxCalls_1596_);
lean_dec(v_test_1595_);
v___x_1608_ = 2;
v___x_1609_ = lean_unsigned_to_nat(1u);
v___x_1610_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1610_, 0, v_initialMask_1594_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
lean_ctor_set_uint8(v___x_1610_, sizeof(void*)*2, v___x_1608_);
v___x_1611_ = lean_apply_2(v_toPure_1600_, lean_box(0), v___x_1610_);
return v___x_1611_;
}
}
}
LEAN_EXPORT void l_Lean_Util_ParamMinimizer_search___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_initialMask_1594_ = stack[0].m_obj;
lean_object* v_test_1595_ = stack[1].m_obj;
lean_object* v_maxCalls_1596_ = stack[2].m_obj;
lean_object* v_inst_1597_ = stack[3].m_obj;
lean_object* v_toBind_1598_ = stack[4].m_obj;
lean_object* v___f_1599_ = stack[5].m_obj;
lean_object* v_toPure_1600_ = stack[6].m_obj;
uint8_t v_____do__lift_1601_ = stack[7].m_num;
lean_object* v_res_1612_;
v_res_1612_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__1(v_initialMask_1594_, v_test_1595_, v_maxCalls_1596_, v_inst_1597_, v_toBind_1598_, v___f_1599_, v_toPure_1600_, v_____do__lift_1601_);
stack->m_obj
 = v_res_1612_;
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed(lean_object* v_initialMask_1613_, lean_object* v_test_1614_, lean_object* v_maxCalls_1615_, lean_object* v_inst_1616_, lean_object* v_toBind_1617_, lean_object* v___f_1618_, lean_object* v_toPure_1619_, lean_object* v_____do__lift_1620_){
_start:
{
uint8_t v_____do__lift_174__boxed_1621_; lean_object* v_res_1622_; 
v_____do__lift_174__boxed_1621_ = lean_unbox(v_____do__lift_1620_);
v_res_1622_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__1(v_initialMask_1613_, v_test_1614_, v_maxCalls_1615_, v_inst_1616_, v_toBind_1617_, v___f_1618_, v_toPure_1619_, v_____do__lift_174__boxed_1621_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search___redArg(lean_object* v_inst_1623_, lean_object* v_initialMask_1624_, lean_object* v_test_1625_, lean_object* v_maxCalls_1626_){
_start:
{
lean_object* v_toApplicative_1627_; lean_object* v_toBind_1628_; lean_object* v_toPure_1629_; lean_object* v___x_1630_; lean_object* v___f_1631_; lean_object* v___f_1632_; lean_object* v___x_1633_; 
v_toApplicative_1627_ = lean_ctor_get(v_inst_1623_, 0);
v_toBind_1628_ = lean_ctor_get(v_inst_1623_, 1);
lean_inc_n(v_toBind_1628_, 2);
v_toPure_1629_ = lean_ctor_get(v_toApplicative_1627_, 1);
lean_inc_n(v_toPure_1629_, 2);
lean_inc(v_test_1625_);
lean_inc_ref(v_initialMask_1624_);
v___x_1630_ = lean_apply_1(v_test_1625_, v_initialMask_1624_);
v___f_1631_ = lean_alloc_closure((void*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1631_, 0, v_toPure_1629_);
v___f_1632_ = lean_alloc_closure((void*)(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1632_, 0, v_initialMask_1624_);
lean_closure_set(v___f_1632_, 1, v_test_1625_);
lean_closure_set(v___f_1632_, 2, v_maxCalls_1626_);
lean_closure_set(v___f_1632_, 3, v_inst_1623_);
lean_closure_set(v___f_1632_, 4, v_toBind_1628_);
lean_closure_set(v___f_1632_, 5, v___f_1631_);
lean_closure_set(v___f_1632_, 6, v_toPure_1629_);
v___x_1633_ = lean_apply_4(v_toBind_1628_, lean_box(0), lean_box(0), v___x_1630_, v___f_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Util_ParamMinimizer_search(lean_object* v_m_1634_, lean_object* v_inst_1635_, lean_object* v_initialMask_1636_, lean_object* v_test_1637_, lean_object* v_maxCalls_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Util_ParamMinimizer_search___redArg(v_inst_1635_, v_initialMask_1636_, v_test_1637_, v_maxCalls_1638_);
return v___x_1639_;
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
